/*
 * Inferno authentication
 */
#include "dat.h"

#define MAXMSG 4096

typedef struct InfPublicKey
{
        RSApub pk;
        char *owner;
} InfPublicKey;

typedef struct InfPrivateKey
{
        RSApriv sk;
        char *owner;
} InfPrivateKey;

typedef struct Certificate
{
        char *sa;
        char *ha;
        char *signer;
        int exp;
        mpint *sig;
} Certificate;

typedef struct Authinfo
{
        InfPrivateKey *mysk;
        InfPublicKey *mypk;
        Certificate *cert;
        InfPublicKey *spk;
        mpint *alpha;
        mpint *p;
} Authinfo;

typedef struct State
{
        int version;
        Authinfo *info;
        mpint *alphar0;
        mpint *alphar1;
        mpint *alphar0r1;
        mpint *r0;
        Certificate *hiscert;
        InfPublicKey *hispk;
        Key *key;
} State;

enum
{
        CHaveVersion,
        CNeedVersion,
        CHaveAlphar0,
        CHaveCert,
        CHavePk,
        CNeedAlphar1,
        CNeedCert,
        CNeedPk,
        CHaveAlphaCert,
        CNeedAlphaCert,
        CHaveOk,
        CNeedOk,

        Maxphase
};

static char *phasenames[Maxphase] =
{
        [CHaveVersion]          "CHaveVersion",
        [CNeedVersion]          "CNeedVersion",
        [CHaveAlphar0]          "CHaveAlphar0",
        [CHaveCert]             "CHaveCert",
        [CHavePk]               "CHavePk",
        [CNeedAlphar1]          "CNeedAlphar1",
        [CNeedCert]             "CNeedCert",
        [CNeedPk]               "CNeedPk",
        [CHaveAlphaCert]        "CHaveAlphaCert",
        [CNeedAlphaCert]        "CNeedAlphaCert",
        [CHaveOk]               "CHaveOk",
        [CNeedOk]               "CNeedOk",

};

static Certificate *sign(InfPrivateKey *sk, int exp, uchar *a, int len);
static int verify(InfPublicKey *pk, Certificate *cert, char *a);
static int rsaverify(mpint *m, mpint *sig, RSApub *key);
static char *pktostr(InfPublicKey *pk);
static char *certtostr(Certificate *cert);
static Certificate *mkcert(char *sa, char *ha, char *signer, int exp, mpint *rsa);
static Certificate *strtocert(char *s);
static InfPublicKey *strtopk(char *s);
static InfPrivateKey *strtosk(char *s);
static Authinfo *keytoauthinfo(Key *k);
static int infrand(mpint *p, mpint *q, mpint *result);
static int mptobase64(mpint *b, char *buf, int len);

static int infauthinit(Proto *, Fsstate *fss)
{
        State *s;
        Key *k;
        Keyinfo ki;

        if(findkey(&k, mkkeyinfo(&ki, fss, nil), "%s", fss->proto->keyprompt) != RpcOk)
                return failure(fss, nil);
        setattrs(fss->attr, k->attr);

        s = emalloc(sizeof(State));
        s->key = k;
        s->info = k->priv;

        fss->ps = s;
        fss->phasename = phasenames;
        fss->maxphase = Maxphase;
        fss->phase = CHaveVersion;

        return RpcOk;
}

static void infauthclose(Fsstate *fss)
{
        State *s;


        s = fss->ps;

        if(s->hiscert)
                free(s->hiscert);
        if(s->hispk)
                free(s->hispk);
        if(s->alphar0r1)
                mpfree(s->alphar0r1);

        if(s->key)
                closekey(s->key);
        free(s);
}

static int infauthaddkey(Key *k, int before)
{
        if((k->priv = keytoauthinfo(k)) == nil) {
                werrstr("malformed key data");
                return -1;
        }

        return replacekey(k, before);
}

static void infauthclosekey(Key *k)
{
        Authinfo *info;

        info = k->priv;

        free(info->mysk);
        free(info->mypk);
        free(info->cert);
        free(info->spk);
        free(info->alpha);
        free(info->p);

        free(info);
}

static int infauthwrite(Fsstate *fss, void *va, uint n)
{
        State *s;
        Certificate *alphacert;
        char *a, *alphabuf;
        long now;
        int i;

        s = fss->ps;
        a = va;
        switch(fss->phase) {
                case CNeedVersion:
                        s->version = atoi((char *)va);
                        if(s->version != 1)
                                return failure(fss, "incompatible authentication protocol");
                        fss->phase = CHaveAlphar0;
                        return RpcOk;
                case CNeedAlphar1:
                        s->alphar1 = strtomp(a, nil, 64, nil);
                        if(mpcmp(s->info->p, s->alphar1) <= 0)
                                return failure(fss, "implausible parameter value");
                        if(mpcmp(s->alphar0, s->alphar1) == 0)
                                return failure(fss, "possible replay attack");
                        fss->phase = CNeedCert;
                        return RpcOk;
                case CNeedCert:
                        s->hiscert = strtocert(a);
                        if(s->hiscert == nil)
                                return failure(fss, "bad certificate syntax");
                        fss->phase = CNeedPk;
                        return RpcOk;
                case CNeedPk:
                        s->hispk = strtopk(a);
                        if(s->hispk == nil)
                                return failure(fss, "bad public key syntax");

                        if(verify(s->info->spk, s->hiscert, a) == 0)
                                return failure(fss, "pk doesn't match certificate");

                        now = time(nil);
                        if(s->hiscert->exp != 0 && s->hiscert->exp <= now)
                                return failure(fss, "certificate expired");
                        fss->phase = CHaveAlphaCert;
                case CNeedAlphaCert:
                        alphacert = strtocert(a);
                        if(alphacert == nil)
                                return failure(fss, "bad certificate syntax");

                        alphabuf = malloc(MAXMSG);
                        i = mptobase64(s->alphar1, alphabuf, MAXMSG);
                        mptobase64(s->alphar0, alphabuf + i, MAXMSG - i);
                        free(alphabuf);
                        if(!verify(s->hispk, alphacert, a))
                                return failure(fss, "signature did not match pk");
                        free(alphacert);

                        s->alphar0r1 = mpnew(0);
                        mpexp(s->alphar1, s->r0, s->info->p, s->alphar0r1);
                        mpfree(s->r0);
                        mpfree(s->alphar0);
                        mpfree(s->alphar1);
                        fss->phase = CHaveOk;
                        return RpcOk;
                case CNeedOk:
                        if(n < 3)
                                return toosmall(fss, 3);
                        if(strcmp("OK", a) != 0)
                                return failure(fss, "not ok");

                        fss->haveai = 1;
                        fss->ai.suid = s->hispk->owner;
                        fss->ai.cuid = s->info->mypk->owner;
                        i = (s->alphar0r1->top + 1) * Dbytes;
                        fss->ai.secret = malloc(i);
                        i = mptobe(s->alphar0r1, fss->ai.secret, i, nil);
                        fss->ai.nsecret = i;
                        fss->phase = Established;
                        return RpcOk;
                default:
                        return phaseerror(fss, "write");
        }
}

static int infauthread(Fsstate *fss, void *va, uint *n)
{
        State *s;
        Certificate *alphacert;
        int i;
        char *a, *buf, *certstr, *pkstr, *alphabuf;
        mpint *low, *p;

        s = fss->ps;
        a = va;

        switch(fss->phase) {
                case CHaveVersion:
                        i = 2;
                        if(*n < i)
                                return toosmall(fss, i);
                        *n = i;
                        strcpy(a, "1");
                        fss->phase = CNeedVersion;
                        return RpcOk;
                case CHaveAlphar0:
                        low = mpnew(0);
                        s->r0 = mpnew(0);
                        s->alphar0 = mpnew(0);
                        buf = malloc(MAXMSG);

                        p = s->info->p;
                        mpright(p, mpsignif(p)/4, low);
                        infrand(low, p, s->r0);
                        mpexp(s->info->alpha, s->r0, p, s->alphar0);
                        mptobase64(s->alphar0, buf, MAXMSG);
                        i = strlen(buf);
                        if(*n < i)
                                return toosmall(fss, i);
                        strcpy(a, buf);
                        *n = strlen(buf) + 1;
                        free(low);
                        free(buf);

                        fss->phase = CHaveCert;
                        return RpcOk;
                case CHaveCert:
                        certstr = certtostr(s->info->cert);
                        i = strlen(certstr) + 1;
                        if(*n < i)
                                return toosmall(fss, i);
                        strcpy(a, certstr);
                        *n = i;
                        free(certstr);
                        fss->phase = CHavePk;
                        return RpcOk;
                case CHavePk:
                        pkstr = pktostr(s->info->mypk);
                        i = strlen(pkstr) + 1;
                        if(*n < i)
                                return toosmall(fss, i);
                        strcpy(a, pkstr);
                        *n = i;
                        free(pkstr);
                        fss->phase = CNeedAlphar1;
                        return RpcOk;
                case CHaveAlphaCert:
                        alphabuf = malloc(MAXMSG);
                        i = mptobase64(s->alphar0, alphabuf, MAXMSG);
                        i += mptobase64(s->alphar1, alphabuf + i, MAXMSG - i);

                        alphacert = sign(s->info->mysk, 0, (uchar *)alphabuf, i);
                        free(alphabuf);

                        alphabuf = certtostr(alphacert);
                        i = strlen(alphabuf) + 1;
                        if(*n < i)
                                return toosmall(fss, i);
                        strcpy(a, alphabuf);
                        *n = i;
                        free(alphabuf);
                        free(alphacert);
                        fss->phase = CNeedAlphaCert;
                        return RpcOk;
                case CHaveOk:
                        i = 3;
                        if(*n < i)
                                return toosmall(fss, i);
                        *n = i;
                        strcpy(a, "OK");
                        fss->phase = CNeedOk;
                        return RpcOk;
                default:
                        return phaseerror(fss, "read");
        }
}

static Certificate *sign(InfPrivateKey *sk, int exp, uchar *a, int len)
{
        Certificate *cert;
        DigestState *ds;
        uchar digest[SHA1dlen];
        char *buf;
        mpint *b, *sig;
        int n;

        buf = malloc(MAXMSG);
        if(buf == nil)
                return nil;

        n = snprint(buf, MAXMSG, "%s %lud", sk->owner, exp);

        ds = sha1(a, len, 0, nil);
        sha1((uchar *)buf, n, digest, ds);

        free(buf);

        b = betomp(digest, SHA1dlen, nil);
        if(b == nil)
                return nil;

        sig = rsadecrypt(&sk->sk, b, nil);

        cert = mkcert("rsa", "sha1", sk->owner, exp, sig);

        mpfree(b);

        return cert;
}

static int verify(InfPublicKey *pk, Certificate *cert, char *a)
{
        DigestState *ds;
        uchar digest[SHA1dlen];
        char *buf;
        mpint *b;
        int n;

        buf = malloc(MAXMSG);
        if(buf == nil)
                return 0;

        n = snprint(buf, MAXMSG, "%s %d", cert->signer, cert->exp);

        if(strcmp(cert->sa, "rsa") || strcmp(cert->ha, "sha1") &&
                strcmp(cert->ha, "sha"))
                return 0;

        ds = sha1((uchar *)a, strlen(a), 0, nil);
        sha1((uchar *)buf, n, digest, ds);

        free(buf);

        b = betomp(digest, SHA1dlen, nil);
        if(b == nil)
                return 0;

        n = rsaverify(b, cert->sig, &pk->pk);

        mpfree(b);

        return n;
}

static int rsaverify(mpint *m, mpint *sig, RSApub *key)
{
        mpint *t;

        t = nil;

        rsaencrypt(key, sig, t);

        return (mpcmp(t, m) == 0);
}

static char *pktostr(InfPublicKey *pk)
{
        char *nstr, *ekstr, *pkstr;

        nstr = malloc(MAXMSG);
        ekstr = malloc(MAXMSG);

        mptobase64(pk->pk.n, nstr, MAXMSG);
        mptobase64(pk->pk.ek, ekstr, MAXMSG);

        pkstr = smprint("rsa\n%s\n%s\n%s\n", pk->owner, nstr, ekstr);

        free(ekstr);
        free(nstr);

        return pkstr;
}

static char *certtostr(Certificate *cert)
{
        char *sigstr, *certstr;

        sigstr = malloc(MAXMSG);
        mptobase64(cert->sig, sigstr, MAXMSG);

        certstr = smprint("%s\n%s\n%s\n%d\n%s\n", cert->sa, cert->ha, cert->signer, cert->exp,
                                sigstr);

        free(sigstr);

        return certstr;
}

static Certificate *mkcert(char *sa, char *ha, char *signer, int exp, mpint *sig)
{
        Certificate *cert;

        cert = malloc(sizeof(Certificate));
        cert->sa = sa;
        cert->ha = ha;
        cert->signer = signer;
        cert->exp = exp;
        cert->sig = sig;

        return cert;
}

static Certificate *strtocert(char *s)
{
        Certificate *cert;
        char *a[5];

        if(s == nil)
                return nil;

        if(getfields(s, a, 5, 0, "\n") < 5)
                return nil;

        cert = malloc(sizeof(Certificate));
        cert->sa = a[0];
        cert->ha = a[1];
        cert->signer = a[2];
        cert->exp = atoi(a[3]);
        strtomp(a[4], nil, 64, cert->sig);

        return cert;
}

static InfPublicKey *strtopk(char *s)
{
        InfPublicKey *pk;
        char *a[4];

        if(s == nil)
                return nil;

        if(getfields(s, a, 4, 0, "\n") < 4)
                return nil;

        if(strcmp(a[0], "rsa"))
                return nil;

        pk = malloc(sizeof(InfPublicKey));
        pk->owner = a[1];
        strtomp(a[2], nil, 64, pk->pk.n);
        strtomp(a[3], nil, 64, pk->pk.ek);

        return pk;
}

static InfPrivateKey *strtosk(char *s)
{
        InfPrivateKey *sk;
        RSApriv *rsask;
        mpint *n, *e, *d, *p, *q;
        char *a[7];

        n = e = d = p = q = nil;

        if(s == nil)
                return nil;

        if(getfields(s, a, 7, 0, "\n") < 7)
                return nil;

        if(strcmp(a[0], "rsa"))
                return nil;

        sk = malloc(sizeof(InfPrivateKey));
        sk->owner = a[1];
        strtomp(a[2], nil, 64, n);
        strtomp(a[3], nil, 64, e);
        strtomp(a[4], nil, 64, d);
        strtomp(a[5], nil, 64, p);
        strtomp(a[6], nil, 64, q);

        rsask = rsafill(n, e, d, p, q);
        sk->sk = *rsask;

        return sk;
}

static Authinfo *keytoauthinfo(Key *k)
{
        Authinfo *info;
        char *a;

        info = malloc(sizeof(Authinfo));

        if((a = _strfindattr(k->privattr, "!sk")) == nil || (info->mysk = strtosk(a)) == nil)
                goto Error;
        if((a = _strfindattr(k->privattr, "!pk")) == nil || (info->mypk = strtopk(a)) == nil)
                goto Error;
        if((a = _strfindattr(k->privattr, "!cert")) == nil || (info->cert = strtocert(a)) == nil)
                goto Error;
        if((a = _strfindattr(k->privattr, "!spk")) == nil || (info->spk = strtopk(a)) == nil)
                goto Error;
        if((a = _strfindattr(k->privattr, "!alpha")) == nil || (info->alpha = strtomp(a, nil, 16, nil)) == nil)
                goto Error;
        if((a = _strfindattr(k->privattr, "!p")) == nil || (info->p = strtomp(a, nil, 16, nil)) == nil)
                goto Error;

        return info;

Error:
        free(info);
        return nil;
}

static int infrand(mpint *p, mpint *q, mpint *result)
{
        mpint *diff, *t, *slop, *r;
        int l;

        diff = mpnew(0);

        if(mpcmp(p, q) > 0) {
                t = p;
                p = q;
                q = t;
        }

        mpsub(q, p, diff);
        if(mpcmp(diff, mptwo) < 0)
                return -1;

        t = mpnew(0);
        slop = mpnew(0);
        mpleft(mpone, mpsignif(diff), t);
        l = mpsignif(t);

        mpmod(t, diff, slop);
        mpfree(t);

        r = mpnew(0);
        do {
                mprand(l, genrandom, r);
        } while(mpcmp(r, slop) < 0);
        mpfree(slop);

        mpmod(r, diff, result);
        mpfree(r);
        mpfree(diff);
        mpadd(result, p, result);

        return 0;
}

// TODO: Could probably use mptoa here
static int mptobase64(mpint *b, char *buf, int len)
{
        uchar *p;
        int n, rv, o;

        n = (b->top + 1) * Dbytes;
        p = malloc(n + 1);
        if(p == nil)
                goto err;

        n = mptobe(b, p + 1, n, nil);
        if(n < 0)
                goto err;

        p[0] = 0;
        if(n != 0 && (p[1] & 0x80)) {
                o = 0;
                n++;
        }
        else
                o = 1;

        rv = enc64(buf, len, p + o, n);
        free(p);

        return rv;

err:
        free(p);
        if(len > 0) {
                *buf = '*';
                return 1;
        }
        return 0;
}

Proto infauth = {
        .name = "infauth",
        .init = infauthinit,
        .write = infauthwrite,
        .read = infauthread,
        .close = infauthclose,
        .addkey = infauthaddkey,
        .closekey = infauthclosekey,
        .keyprompt = "user?",
};
