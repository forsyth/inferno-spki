/*
 * Inferno authentication
 */
#include "std.h"
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

static Certificate *sign(InfPrivateKey *sk, int exp, uchar *a, int len);
static int verify(InfPublicKey *pk, Certificate *cert, char *a);
static int infrsaverify(mpint *m, mpint *sig, RSApub *key);
static char *pktostr(InfPublicKey *pk);
static char *certtostr(Certificate *cert);
static Certificate *mkcert(char *sa, char *ha, char *signer, int exp, mpint *sig);
static Certificate *strtocert(char *s);
static InfPublicKey *strtopk(char *s);
static InfPrivateKey *strtosk(char *s);
static Authinfo *keytoauthinfo(Key *k);
static int infrand(mpint *p, mpint *q, mpint *result);
static int mptobase64(mpint *b, char *buf, int len);

static int infauthclient(Conv *c)
{
	Key *k;
	Attr *attr;
	Authinfo *info;
	Certificate *hiscert, *alphacert;
	InfPublicKey *hispk;
	mpint *p, *low, *r0, *alphar0, *alphar1, *alphar0r1;
	char *buf, *alphabuf;
	uchar *cvb;
	int ret, n;
	long now;

	k = nil;
	attr = nil;
	ret = -1;
	alphar0 = alphar1 = alphar0r1 = r0 = low = p = nil;

	buf = malloc(MAXMSG);
	alphabuf = malloc(MAXMSG);

	c->state = "find key";
	k = keyfetch(c, "%A %s", attr, c->proto->keyprompt);
	if(k == nil) {
		info = nil;
		goto out;
	}

	info = k->priv;

	if(info->p == nil) {
		werrstr("missing diffie hellman mod");
		goto out;
	}

	if(info->alpha == nil) {
		werrstr("missing diffie hellman base");
		goto out;
	}

	if(info->mysk == nil || info->mypk == nil || info->cert == nil || info->spk == nil) {
		werrstr("invalid authentication information");
		goto out;
	}

	c->state = "write version";
	if(convprint(c, "1") < 0)
		goto out;
	
	c->state = "read version";
	if(convreadm(c, &buf) < 0)
		goto out;
	if(atoi(buf) != 1) {
		werrstr("incompatible authentication protocol");
		goto out;
	}

	low = mpnew(0);
	r0 = mpnew(0);
	alphar0 = mpnew(0);
	alphar0r1 = mpnew(0);

	c->state = "write alphar0";
	p = info->p;
	mpright(p, mpsignif(p)/4, low);
	infrand(low, p, r0);
	mpexp(info->alpha, r0, p, alphar0);
	mptobase64(alphar0, buf, MAXMSG);
	if(convprint(c, "%s", buf) < 0)
		goto out;
	
	c->state = "write cert";
	if(convprint(c, "%s", certtostr(info->cert)) < 0)
		goto out;
	
	c->state = "write pk";
	if(convprint(c, "%s", pktostr(info->mypk)) < 0)
		goto out;

	c->state = "read alphar1";
	if(convreadm(c, &buf) < 0)
		goto out;
	
	alphar1 = strtomp(buf, nil, 64, nil);
	if(mpcmp(info->p, alphar1) <= 0) {
		werrstr("implausible parameter value");
		goto out;
	}
	if(mpcmp(alphar0, alphar1) == 0) {
		werrstr("possible replay attack");
		goto out;
	}
	
	c->state = "read cert";
	if(convreadm(c, &buf) < 0)
		goto out;
	
	hiscert = strtocert(buf);
	if(hiscert == nil) {
		werrstr("bad certificate syntax");
		goto out;
	}
	
	c->state = "read pk";
	if(convreadm(c, &buf) < 0)
		goto out;
	
	hispk = strtopk(buf);
	if(hispk == nil) {
		werrstr("bad public key syntax");
		goto out;
	}

	if(verify(info->spk, hiscert, buf) == 0) {
		werrstr("pk doesn't match certificate");
		goto out;
	}

	now = time(nil);
	if(hiscert->exp != 0 && hiscert->exp <= now) {
		werrstr("certificate expired");
		goto out;
	}
	free(hiscert);

	c->state = "write alpha cert";
	n = mptobase64(alphar0, alphabuf, MAXMSG);
	n += mptobase64(alphar1, alphabuf + n, MAXMSG - n);
	alphacert = sign(info->mysk, 0, (uchar *)alphabuf, n);
	memset(alphabuf, 0, sizeof(*alphabuf));
	if(convprint(c, "%s", certtostr(alphacert)) < 0)
		goto out;
	
	c->state = "read alpha cert";
	if(convreadm(c, &buf) < 0)
		goto out;
	alphacert = strtocert(buf);
	if(alphacert == nil) {
		werrstr("bad certificate syntax");
		goto out;
	}

	n = mptobase64(alphar1, alphabuf, MAXMSG);
	n += mptobase64(alphar0, alphabuf + n, MAXMSG - n);
	if(!verify(hispk, alphacert, alphabuf)) {
		werrstr("signature did not match pk");
		goto out;
	}
	free(alphabuf);
	free(alphacert);
	free(hispk);

	mpexp(alphar1, r0, info->p, alphar0r1);
	n = mptobe(alphar0r1, nil, MAXMSG, &cvb);
	c->attr = addattr(c->attr, "secret=%H", cvb);

	c->state = "write ok";
	if(convprint(c, "OK") < 0)
		goto out;
	
	c->state = "read ok";
	while(convreadm(c, &buf) >= 0 && strcmp(buf, "OK"))
		;
	ret = 0;

out:
	keyclose(k);

	free(buf);
	if(low != nil) {
		mpfree(low);
		mpfree(r0);
		mpfree(alphar0);
		mpfree(alphar1);
		mpfree(alphar0r1);
	}

	return ret;
}

static int infauthcheck(Key *k)
{
	if((k->priv = keytoauthinfo(k)) == nil) {
		werrstr("malformed key data");
		return -1;
	}

	return 0;
}

static void infauthclose(Key *k)
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

	k->priv = nil;
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

	n = infrsaverify(b, cert->sig, &pk->pk);

	mpfree(b);

	return n;
}

static int infrsaverify(mpint *m, mpint *sig, RSApub *key)
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

	certstr = smprint("%s\n%s\n%s\n%d\n%s\n", cert->sa, cert->ha, cert->signer, cert->exp, sigstr);

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

	if((a = strfindattr(k->privattr, "!sk")) == nil || 
		(info->mysk = strtosk(a)) == nil)
			goto error;
	if((a = strfindattr(k->privattr, "!pk")) == nil ||
		(info->mypk = strtopk(a)) == nil)
			goto error;
	if((a = strfindattr(k->privattr, "!cert")) == nil || 
		(info->cert = strtocert(a)) == nil)
			goto error;
	if((a = strfindattr(k->privattr, "!spk")) == nil ||
		(info->spk = strtopk(a)) == nil)
			goto error;
	if((a = strfindattr(k->privattr, "!alpha")) == nil ||
		(info->alpha = strtomp(a, nil, 16, nil)) == nil)
			goto error;
	if((a = strfindattr(k->privattr, "!p")) == nil ||
		(info->p = strtomp(a, nil, 16, nil)) == nil)
			goto error;

	return info;

error:
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

static Role infauthroles[] =
{
	"client",	infauthclient,
	0
};

Proto infauth = {
	"infauth",
	infauthroles,
	// TODO: Should this be the keyprompt?
	"user?",
	infauthcheck,
	infauthclose
};

