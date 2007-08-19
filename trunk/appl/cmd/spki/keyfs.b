implement Keyfs;

#
# Copyright © 2004 Vita Nuova Holdings Limited.  All rights reserved.
#

# 
# pk/name/...
# sk/name/...
# cred/name/{issuer, subject, type, tag, validity, signed}
#

include "sys.m";
	sys: Sys;
	Qid: import Sys;

include "draw.m";

include "string.m";
	str: String;

include "keyring.m";
	kr: Keyring;
	AESbsize, AESstate: import kr;

include "rand.m";
	rand: Rand;

include "bufio.m";
	bufio: Bufio;
	Iobuf: import bufio;

include "sexprs.m";
	sexprs: Sexprs;
	Sexp: import sexprs;

include "spki.m";
	spki: SPKI;
	Toplev, Key, Name, Cert, Subject, Signature, Valid: import spki;

include "encoding.m";
	base16: Encoding;
	base64: Encoding;

include "styx.m";
	styx: Styx;
	Tmsg, Rmsg: import styx;

include "styxservers.m";
	styxservers: Styxservers;
	Fid, Styxserver, Navigator, Navop: import styxservers;
	Enotfound, Eperm, Ebadarg, Edot: import styxservers;

include "arg.m";

Keyfs: module
{
	init:   fn(nil: ref Draw->Context, nil: list of string);
};

Spkikey: adt
{
	x:      int;    # table index
	name:   string;
	pk:     ref Key;
	sk:     ref Key;
	cert:   ref Cert;
	path:   big;
};

Qroot, Qnew, Qpk, Qsk, Qcred, Qpkname, Qskname, Qcredname, 
	Qalg, Qcert, Qissuer, Qsubject, Qtype, Qtag, Qtransport, 
	Qvalidity, Qsigned, Qpubkey, Qprivkey: con iota;

pkfiles := array[] of {
	(Qpubkey, "key"),
	(Qalg, "alg")
};

skfiles := array[] of {
	(Qprivkey, "key"),
	(Qalg, "alg")
};

credcertfiles := array[] of {
	(Qcert, "cert"),	# whole thing
	(Qissuer, "issuer"),
	(Qsubject, "subject"),
	(Qtype, "type"),
	(Qtag, "tag"),
	(Qvalidity, "valid"),
	(Qtransport, "transport"),      # whole thing in transport format
	(Qsigned, "signed")
};

credpkfiles := array[] of {
	(Qpubkey, "pubkey"),
	(Qtype, "type")
};

credskfiles := array[] of {
	(Qtype, "type")
};

ctlfiles := array[] of {
	(Qnew, "new")
};

dirs := array[] of {
	(Qpk, "pk"),    # public keys
	(Qsk, "sk"),    # secret keys
	(Qcred, "cred") # everything
};

Maxsecret: con 255;
Maxname: con 255;
Maxfail: con 50;
keys: array of ref Spkikey;
Never: con 0;   # expiry time

Eremoved: con "name has been removed";

pathgen := 0;
keyversion := 0;
user: string;
now: int;

usage()
{
	sys->fprint(sys->fildes(2), "Usage: keyfs [-D] [-m mountpoint] [keyfile]\n");
	raise "fail:usage";
}

nomod(s: string)
{
	sys->fprint(sys->fildes(2), "keyfs: can't load %s: %r\n", s);
	raise "fail:load";
}

init(nil: ref Draw->Context, args: list of string)
{
	sys = load Sys Sys->PATH;
	sys->pctl(Sys->NEWPGRP, nil);

	str = load String String->PATH;

	kr = load Keyring Keyring->PATH;
	if(kr == nil)
		nomod(Keyring->PATH);
	styx = load Styx Styx->PATH;
	if(styx == nil)
		nomod(Styx->PATH);
	styxservers = load Styxservers Styxservers->PATH;
	if(styxservers == nil)
		nomod(Styxservers->PATH);
	rand = load Rand Rand->PATH;
	if(rand == nil)
		nomod(Rand->PATH);
	bufio = load Bufio Bufio->PATH;
	if(bufio == nil)
		nomod(Bufio->PATH);
	sexprs = load Sexprs Sexprs->PATH;
	if(sexprs == nil)
		nomod(Sexprs->PATH);
	spki = load SPKI SPKI->PATH;
	if(spki == nil)
		nomod(SPKI->PATH);

	sexprs->init();
	spki->init();

	styx->init();
	styxservers->init(styx);
	rand->init(sys->millisec());

	arg := load Arg Arg->PATH;
	if(arg == nil)
		nomod(Arg->PATH);
	arg->init(args);
	arg->setusage("keyfs [-m mntpt] [-D] [-n nvramfile] [keyfile]");
	mountpt := "/mnt/keys";
	keyfile := "/keydb/spki";
	nvram: string;
	while((o := arg->opt()) != 0)
		case o {
		'm' =>
			mountpt = arg->earg();
		'D' =>
			styxservers->traceset(1);
		'n' =>
			nvram = arg->earg();
		* =>
			usage();
		}
	args = arg->argv();
	arg = nil;

	if(args != nil)
		keyfile = hd args;

	pwd, err: string;
	if(nvram != nil){
		pwd = rf(nvram);
		if(pwd == nil)
			fatal(sys->sprint("can't read %s: %r", nvram));
	}
	if(pwd == nil){
		(pwd, err) = readconsline("Key: ", 1);
		if(pwd == nil || err == "exit")
			exit;
		if(err != nil)
			fatal(sys->sprint("couldn't get key: %s", err));
		pwd0 := pwd;
		(pwd, err) = readconsline("Confirm key: ", 1);
		if(pwd == nil || err == "exit")
			exit;
		if(pwd != pwd0)
			fatal("key mismatch");
		for(i := 0; i < len pwd0; i++)
			pwd0[i] = ' ';  # clear it out
	}

	thekey = hashkey(pwd);
	for(i:=0; i<len pwd; i++)
		pwd[i] = ' ';   # clear it out

	sys->pctl(Sys->NEWPGRP|Sys->FORKFD, nil);       # immediately avoid sharing keyfd

	readkeys(keyfile);

	user = rf("/dev/user");
	if(user == nil)
		user = "keyfs";

	fds := array[2] of ref Sys->FD;
	if(sys->pipe(fds) < 0)
		fatal(sys->sprint("can't create pipe: %r"));

	navops := chan of ref Navop;
	spawn navigator(navops);

	(tchan, srv) := Styxserver.new(fds[0], Navigator.new(navops), big Qroot);
	fds[0] = nil;

	pidc := chan of int;
	spawn serveloop(tchan, srv, pidc, navops, keyfile);
	<-pidc;

	if(sys->mount(fds[1], nil, mountpt, Sys->MREPL|Sys->MCREATE, nil) < 0)
		fatal(sys->sprint("mount on %s failed: %r", mountpt));
}

rf(f: string): string
{
	fd := sys->open(f, Sys->OREAD);
	if(fd == nil)
		return nil;
	b := array[256] of byte;
	n := sys->read(fd, b, len b);
	if(n < 0)
		return nil;
	return string b[0:n];
}

quit(err: string)
{
	fd := sys->open("/prog/"+string sys->pctl(0, nil)+"/ctl", Sys->OWRITE);
	if(fd != nil)
		sys->fprint(fd, "killgrp");
	if(err != nil)
		raise "fail:"+err;
	exit;
}

fatal(s: string)
{
	error(s);
	quit("error");
}

error(s: string)
{
	sys->fprint(sys->fildes(2), "%s\n", s);
}

thekey: array of byte;

hashkey(s: string): array of byte
{
	key := array of byte s;
	skey := array[Keyring->SHA1dlen] of byte;
	sha := kr->sha1(array of byte "aescbc file", 11, nil, nil);
	kr->sha1(key, len key, skey, sha);
	for(i:=0; i<len key; i++)
		key[i] = byte 0;	# clear it out

	return skey[0:AESbsize];
}

readconsline(prompt: string, raw: int): (string, string)
{
	fd := sys->open("/dev/cons", Sys->ORDWR);
	if(fd == nil)
		return (nil, sys->sprint("can't open cons: %r"));
	sys->fprint(fd, "%s", prompt);
	fdctl: ref Sys->FD;
	if(raw){
		fdctl = sys->open("/dev/consctl", sys->OWRITE);
		if(fdctl == nil || sys->fprint(fdctl, "rawon") < 0)
			return (nil, sys->sprint("can't open consctl: %r"));
	}
	line := array[256] of byte;
	o := 0;
	     err: string;
	buf := array[1] of byte;
  Read:
	while((r := sys->read(fd, buf, len buf)) > 0){
		c := int buf[0];
		case c {
		16r7F =>
			err = "interrupt";
			break Read;
		'\b' =>
			if(o > 0)
				o--;
		'\n' or '\r' or 16r4 =>
			break Read;
		* =>
			if(o > len line){
				err = "line too long";
				break Read;
			}
			line[o++] = byte c;
		}
	}
	sys->fprint(fd, "\n");
	if(r < 0)
		err = sys->sprint("can't read cons: %r");
	if(raw)
		sys->fprint(fdctl, "rawoff");
	if(err != nil)
		return (nil, err);
	return (string line[0:o], err);
}

serveloop(tchan: chan of ref Tmsg, srv: ref Styxserver, pidc: chan of int, navops: chan of ref Navop, keyfile: string)
{
	pidc <-= sys->pctl(Sys->FORKNS|Sys->NEWFD, 1::2::srv.fd.fd::nil);

	while((gm := <-tchan) != nil) {

		now = time();
		pick m := gm {

		Readerror =>
			fatal(sys->sprint("mount read error: %s", m.error));

		Create =>
			(c, mode, nil, err) := srv.cancreate(m);
			if(c == nil){
				srv.reply(ref Rmsg.Error(m.tag, err));
				break;
			}
			srv.reply(ref Rmsg.Error(m.tag, Eperm));

		Read =>
			(c, err) := srv.canread(m);
			if(c == nil) {
				srv.reply(ref Rmsg.Error(m.tag, err));
				break;
			}
			if(c.qtype & Sys->QTDIR) {
				srv.read(m);    # does readdir
				break;
			}
			k := findspkikeypath(c.path, nil);
			if(k == nil) {
				srv.reply(ref Rmsg.Error(m.tag, Eremoved));
				break;
			}
			case TYPE(c.path) {
			Qnew =>
				srv.reply(styxservers->readstr(m, nil));
			Qpubkey =>
				srv.reply(styxservers->readstr(m, k.pk.text()));
			Qprivkey =>
				srv.reply(styxservers->readstr(m, k.sk.text()));
			Qcert =>
				srv.reply(styxservers->readstr(m, k.cert.text()));
			Qalg =>
				if(k.pk != nil)
					srv.reply(styxservers->readstr(m, k.pk.sigalg()));
				else 
					srv.reply(styxservers->readstr(m, k.sk.sigalg()));
			Qissuer =>
				srv.reply(styxservers->readstr(m, k.cert.issuer.text()));
			Qsubject =>
				srv.reply(styxservers->readstr(m, k.cert.subject.text()));
			Qtype =>
				if(k.cert != nil)
					srv.reply(styxservers->readstr(m, "cert"));
				else if(k.pk != nil)
					srv.reply(styxservers->readstr(m, "public key"));
				else
					srv.reply(styxservers->readstr(m, "secret key"));
			Qtag =>
				s: string;
				pick d := k.cert {
				A or KH or O =>
					s = d.tag.text();
				}
				srv.reply(styxservers->readstr(m, s));
			Qtransport =>
				srv.reply(styxservers->readbytes(m, k.cert.sexp().pack()));
			Qvalidity =>
				if(k.cert.valid != nil)
					s := (*k.cert.valid).text();
				else
					s = "";
				srv.reply(styxservers->readstr(m, s));
			Qsigned =>
				# might be more than one, found in various sequences
				srv.reply(styxservers->readstr(m, nil));
			* =>
				srv.reply(ref Rmsg.Error(m.tag, Eperm));
			}
	       Write =>
			(c, merr) := srv.canwrite(m);
			if(c == nil){
				srv.reply(ref Rmsg.Error(m.tag, merr));
				break;
			}
		  Case:
			case TYPE(c.path) {
			Qnew =>
				(s, t) := str->splitl(string m.data, "=");
				if(t == nil) {
					srv.reply(ref Rmsg.Error(m.tag, "no name given"));
					break;
				}

				name := trim(s);
				t = str->drop(t, "=");
				t = trim(t);

				while(t != "") {

					se: ref Sexp;
					msg: string;
					(se, t, msg) = Sexp.parse(t);
						if(msg != nil) {
							srv.reply(ref Rmsg.Error(m.tag, msg));
							break Case;
						}

					(toplev, err) := spki->parse(se);
					if(err != nil) {
						srv.reply(ref Rmsg.Error(m.tag, err));
						break Case;
					}

					pick s := toplev {
						C =>
							cert := s.v;
							if(cert == nil) {
								srv.reply(ref Rmsg.Error(m.tag, "bad certificate"));
								continue;
							}

							c := findspkikeyname(name, "cert");
							if(c != nil) {
								srv.reply(ref Rmsg.Error(m.tag, 
										"certificate name already exists"));
								continue;
							}

							c = newspkikey(name, toplev, nil);
							writekeys(keyfile);
						K =>
							key := s.v;
							if(key == nil) {
								srv.reply(ref Rmsg.Error(m.tag, "bad key"));
								continue;
							}

							k: ref Spkikey;
						if(key.pk != nil)
							k = findspkikeyname(name, "pk");
						if(k != nil) {
							srv.reply(ref Rmsg.Error(m.tag, "publickey name already exists"));
							continue;
						}

						if(key.sk != nil)
							k = findspkikeyname(name, "sk");
						if(k != nil) {
							srv.reply(ref Rmsg.Error(m.tag, "secretkey name already exists"));
							continue;
						}

						k = newspkikey(name, toplev, nil);
						writekeys(keyfile);
					}
				}
			* =>
				srv.reply(ref Rmsg.Error(m.tag, Eperm));
				continue;
			}
			srv.reply(ref Rmsg.Write(m.tag, len m.data));

		Remove =>
			c := srv.getfid(m.fid);
			if(c == nil){
				srv.remove(m);  # let it diagnose the errors
				break;
			}
			case TYPE(c.path) {
			Qpkname =>
				k := findspkikeypath(c.path, "pk");
				if(k == nil) {
					srv.reply(ref Rmsg.Error(m.tag, Eremoved));
					break;
				}
				removespkikey(k, "pk");
				writekeys(keyfile);
				srv.delfid(c);
				srv.reply(ref Rmsg.Remove(m.tag));
			Qskname =>
				k := findspkikeypath(c.path, "sk");
				if(k == nil) {
					srv.reply(ref Rmsg.Error(m.tag, Eremoved));
					break;
				}
				removespkikey(k, "sk");
				writekeys(keyfile);
				srv.delfid(c);
				srv.reply(ref Rmsg.Remove(m.tag));
			Qcredname =>
				k := findspkikeypath(c.path, nil);
				if(k == nil) {
					srv.reply(ref Rmsg.Error(m.tag, Eremoved));
					break;
				}
				removespkikey(k, nil);
				writekeys(keyfile);
				srv.delfid(c);
				srv.reply(ref Rmsg.Remove(m.tag));
			* =>
				srv.remove(m);  # let it reject it
			}
		Wstat =>
			# rename key
			c := srv.getfid(m.fid);
			if(c == nil){
				srv.default(gm);	# let it reject it
				break;
			}
			case TYPE(c.path) {
			Qpkname =>
				k := findspkikeypath(c.path, "pk");
				if(k == nil) {
					srv.reply(ref Rmsg.Error(m.tag, Eremoved));
					break;
				}
				if((new := m.stat.name) == nil) {
					srv.default(gm);
					break;
				}
				if(new == "." || new == "..") {
					srv.reply(ref Rmsg.Error(m.tag, Edot));
					break;
				}
				if(findspkikeyname(new, "pk") != nil) {
					srv.reply(ref Rmsg.Error(m.tag, "key name already exists"));
					break;
				}
				if((knew := findspkikeyname(new, nil)) != nil) {
					knew.pk = k.pk;
					k.pk = nil;
					if(k.cert == nil && k.sk == nil)
						keys[k.x] = nil;
				}
				else {
					newkey: ref Key;
					newkey.pk = k.pk.pk;
					newkey.sk = nil;
					newkey.halg = k.pk.halg;
					newkey.hash = k.pk.hash;
					knew = newspkikey(new, ref Toplev.K(newkey), nil);
					k.pk = nil;
					if(k.cert == nil && k.sk == nil)
						keys[k.x] = nil;
				}
				writekeys(keyfile);
				srv.reply(ref Rmsg.Wstat(m.tag));
			Qskname =>
				k := findspkikeypath(c.path, "sk");
				if(k == nil) {
					srv.reply(ref Rmsg.Error(m.tag, Eremoved));
					break;
				}
				if((new := m.stat.name) == nil) {
					srv.default(gm);
					break;
				}
				if(new == "." || new == "..") {
					srv.reply(ref Rmsg.Error(m.tag, Edot));
					break;
				}
				if(findspkikeyname(new, "sk") != nil) {
					srv.reply(ref Rmsg.Error(m.tag, "key name already exists"));
					break;
				}
				if((knew := findspkikeyname(new, nil)) != nil) {
					knew.sk = k.sk;
					k.sk = nil;
					if(k.cert == nil && k.pk == nil)
						keys[k.x] = nil;
				}
				else {
					newkey: ref Key;
					newkey.pk = nil;
					newkey.sk = k.sk.sk;
					newkey.halg = k.sk.halg;
					newkey.hash = k.sk.hash;
					knew = newspkikey(new, ref Toplev.K(newkey), nil);
					k.sk = nil;
					if(k.cert == nil && k.pk == nil)
						keys[k.x] == nil;
				}
				writekeys(keyfile);
				srv.reply(ref Rmsg.Wstat(m.tag));
			Qcredname =>
				k := findspkikeypath(c.path, nil);
				if(k == nil) {
					srv.reply(ref Rmsg.Error(m.tag, Eremoved));
					break;
				}
				if((new := m.stat.name) == nil) {
					srv.default(gm);
					break;
				}
				if(new == "." || new == "..") {
					srv.reply(ref Rmsg.Error(m.tag, Edot));
					break;
				}
				if(findspkikeyname(new, nil) != nil) {
					srv.reply(ref Rmsg.Error(m.tag, "key name already exists"));
					break;
				}
				k.name = new;
				writekeys(keyfile);
				srv.reply(ref Rmsg.Wstat(m.tag));
			* =>
				srv.default(gm);
			}
		* =>
			srv.default(gm);
		}
	}
	navops <-= nil;	 # shut down navigator
}

trim(s: string): string
{
	t := str->drop(s, " \t\n");
	if(t == nil)
		return nil;
	(u, v) := str->splitr(t, "^ \t\n");
	if(u == nil)
		return t;
	return u;
}

isnumeric(s: string): int
{
	for(i:=0; i<len s; i++)
		if(!(s[i]>='0' && s[i]<='9'))
			return 0;
	return i>0;
}

TYPE(path: big): int
{
	return int path & 16r1F;
}

INDEX(path: big): int
{
	return (int (path & big 16rFFFFFF00) >> 8);
}

findspkikeypath(path: big, spkitype: string): ref Spkikey
{
	i := INDEX(path);
	if(i >= len keys || (k := keys[i]) == nil || k.path != (path & ~big 16r1F))
		return nil;

	case spkitype {
		"pk" =>
			if(k.pk != nil)
				return k;
		"sk" =>
			if(k.sk != nil)
				return k;
		"cert" =>
			if(k.cert != nil)
				return k;
		* =>
			return k;
	}

	return nil;
}

findspkikeyname(name: string, spkitype: string): ref Spkikey
{
	for(i := 0; i < len keys; i++)
		if((k := keys[i]) != nil && k.name == name) {
			case spkitype {
				"pk" =>
					if(k.pk != nil)
						return k;
				"sk" =>
					if(k.sk != nil)
						return k;
				"cert" =>
					if(k.cert != nil)
						return k;
				* =>
					return k;
			}
		}

	return nil;
}

newspkikey(name: string, t: ref Toplev, k: ref Spkikey): ref Spkikey
{
	if(k == nil) {
		knew := findspkikeyname(name, nil);
		if(knew != nil) {
			pick s := t {
				C =>
					knew.cert = s.v;
				K =>
					key := s.v;
					if(key.pk != nil)
						knew.pk = key;
					if(key.sk != nil)
						knew.sk = key;
			}
			return knew;
		}
	}

	for(i := 0; i < len keys; i++)
		if(keys[i] == nil)
			break;
	if(i >= len keys)
		keys = (array[i+16] of ref Spkikey)[0:] = keys;
	path := big ((big pathgen++ << 32) | (big i << 8));
	if(k == nil) {
		pick x := t {
			C =>
				k = ref Spkikey(i, name, nil, nil, x.v, path);
			K =>
				if(x.v.pk != nil)
					k = ref Spkikey(i, name, x.v, nil, nil, path);
				if(x.v.sk != nil)
					k = ref Spkikey(i, name, nil, x.v, nil, path);
		}
	}
	else {
		k.x = i;
		k.path = path;
	}
	keys[i] = k;

	return k;
}

removespkikey(k: ref Spkikey, spkitype: string)
{
	if(k != nil) {
		case spkitype {
			"pk" =>
				k.pk = nil;
				if(k.sk == nil && k.cert == nil)
					keys[k.x] = nil;
			"sk" =>
				k.sk = nil;
				if(k.pk == nil && k.cert == nil)
					keys[k.x] = nil;
			"cert" =>
				k.cert = nil;
				if(k.pk == nil && k.sk == nil)
					keys[k.x] = nil;
			* =>
				keys[k.x] = nil;
		}
	}
}

dirslot(n: int): int
{
	for(i := 0; i < len keys; i++) {
		k := keys[i];
		if(k != nil) {
			if(n == 0)
				break;
			n--;
		}
	}
	return i;
}

dir(qid: Sys->Qid, name: string, length: big, perm: int): ref Sys->Dir
{
	d := ref sys->zerodir;

	d.qid = qid;
	if(qid.qtype & Sys->QTDIR)
		perm |= Sys->DMDIR;
	d.mode = perm;
	d.name = name;
	d.uid = user;
	d.gid = user;
	d.length = length;
	d.atime = now;
	d.mtime = now;

	return d;
}

dirgen(p: big, name: string, k: ref Spkikey): (ref Sys->Dir, string)
{
	case t := TYPE(p) {
	Qroot =>
		return (dir(Qid(big Qroot, keyversion,Sys->QTDIR), "/", big 0, 8r755), nil);
	Qsk =>
		return (dir(Qid(p, 0, Sys->QTDIR), name, big 0, 8r700), nil);
	Qpk or Qcred =>
		return (dir(Qid(p, 0, Sys->QTDIR), name, big 0, 8r755), nil);
	Qpkname or Qskname or Qcredname =>
		if(name == nil){
			if(k == nil){
				k = findspkikeypath(p, nil);
				if(k == nil)
					return (nil, Enotfound);
			}
			name = k.name;
		}
		return (dir(Qid(p, 0, Sys->QTDIR), name, big 0, 8r755), nil);
	* =>
		return (dir(Qid(p,0,Sys->QTFILE), name, big 0, 8r600), nil);
	}
}

navigator(navops: chan of ref Navop)
{
	while((m := <-navops) != nil) {
	   Pick:
		pick n := m {
		Stat =>
			n.reply <-= dirgen(n.path, nil, nil);
		Walk =>
			case TYPE(n.path) {
			Qroot =>
				if(n.name == "..") {
					n.reply <-= dirgen(n.path, nil, nil);
					break;
				}
				for(i := 0; i < len dirs; i++) {
					(dtype, name) := dirs[i];
					if(n.name == name) {
						n.reply <-= dirgen((n.path & ~big 16r1F) | big dtype, name, nil);
						break Pick;
					}
				}
				for(j := 0; j < len ctlfiles; j++) {
					(ftype, name) := ctlfiles[j];
					if(n.name == name) {
						n.reply <-= dirgen((n.path & ~big 16r1F) | big ftype, name, nil);
						break Pick;
					}
				}
				n.reply <-= (nil, Enotfound);
			Qpk =>
				if(n.name == "..") {
					n.reply <-= dirgen(big Qroot, nil, nil);
					break;
				}
				k := findspkikeyname(n.name, "pk");
				if(k == nil) {
					n.reply <-= (nil, Enotfound);
					break;
				}
				n.reply <-= dirgen(k.path & ~big 16r1F | big Qpkname, k.name, k);
			Qsk =>
				if(n.name == "..") {
					n.reply <-= dirgen(big Qroot, nil, nil);
					break;
				}
				k := findspkikeyname(n.name, "sk");
				if(k == nil) {
					n.reply <-= (nil, Enotfound);
					break;
				}
				n.reply <-= dirgen(k.path & ~big 16r1F | big Qskname, k.name, k);
			Qcred =>
				if(n.name == "..") {
					n.reply <-= dirgen(big Qroot, nil, nil);
					break;
				}
				k := findspkikeyname(n.name, nil);
				if(k == nil) {
					n.reply <-= (nil, Enotfound);
					break;
				}
				n.reply <-= dirgen(k.path & ~big 16r1F | big Qcredname, k.name, k);
			Qpkname =>
				if(n.name == "..") {
					n.reply <-= dirgen(big Qpk, nil, nil);
					break;
				}
				for(j := 0; j < len pkfiles; j++) {
					(ftype, name) := pkfiles[j];
					if(n.name == name) {
						n.reply <-= dirgen(n.path & ~big 16r1F | big ftype, name, nil);
						break Pick;
					}
				}
				n.reply <-= (nil, Enotfound);
			Qskname =>
				if(n.name == "..") {
					n.reply <-= dirgen(big Qsk, nil, nil);
					break;
				}
				for(j := 0; j < len skfiles; j++) {
					(ftype, name) := skfiles[j];
					if(n.name == name) {
						n.reply <-= dirgen(n.path & ~big 16r1F | big ftype, name, nil);
						break Pick;
					}
				}
				n.reply <-= (nil, Enotfound);
			Qcredname =>
				if(n.name == "..") {
					n.reply <-= dirgen(big Qcred, nil, nil);
					break;
				}

				k := findspkikeypath(n.path, nil);
				if(k == nil) {
					n.reply <-= (nil, Eremoved);
					break;
				}

				if(k.cert != nil) {
					for(j := 0; j < len credcertfiles; j++) {
						(ftype, name) := credcertfiles[j];
						if(n.name == name) {
							n.reply <-= dirgen((n.path & ~big 16r1F) | big ftype, name, nil);
							break Pick;
						}
					}
				}
				if(k.pk != nil) {
					for(j := 0; j < len credpkfiles; j++) {
						(ftype, name) := credpkfiles[j];
						if(n.name == name) {
							n.reply <-= dirgen((n.path & ~big 16r1F) | big ftype, name, nil);
							break Pick;
						}
					}
				}

				if(k.sk != nil) {
					for(j := 0; j < len credskfiles; j++) {
						(ftype, name) := credskfiles[j];
						if(n.name == name) {
							n.reply <-= dirgen((n.path & ~big 16r1F) | big ftype, name, nil);
							break Pick;
						}
					}
				}
				n.reply <-= (nil, Enotfound);
			* =>
				if(n.name != "..") {
					n.reply <-= (nil, Enotfound);
					break;
				}
				n.reply <-= dirgen((n.path & ~big 16r1F) | big Qroot, nil, nil); # parent directory
			}
	       Readdir =>
			case TYPE(n.path) {
			Qroot =>
				for(i := n.offset; --n.count >= 0 && i < len dirs; i++) {
					 (dtype, name) := dirs[i];
					 n.reply <-= dirgen(n.path & ~big 16r1F | big dtype, name, nil);
				}
				for(j := n.offset; --n.count >= 0 && j < len ctlfiles; j++) {
					(ftype, name) := ctlfiles[j];
					n.reply <-= dirgen((n.path & ~big 16r1F) | big ftype, name, nil);
				}
				n.reply <-= (nil, nil);
			Qpk =>
				if(n.offset == 0) {
					for(j := dirslot(n.offset); --n.count >= 0 && j < len keys; j++)
						if((k := keys[j]) != nil && k.pk != nil)
							n.reply <-= dirgen(k.path & ~big 16r1F | big Qpkname, k.name, k);
				}
				n.reply <-= (nil, nil);
			Qsk =>
				if(n.offset == 0) {
					for(j := dirslot(n.offset); --n.count >= 0 && j < len keys; j++)
						if((k := keys[j]) != nil && k.sk != nil)
							n.reply <-= dirgen(k.path & ~big 16r1F | big Qskname, k.name, k);
				}
				n.reply <-= (nil, nil);
			Qcred =>
				for(j := dirslot(n.offset); --n.count >= 0 && j < len keys; j++)
					if((k := keys[j]) != nil)
						n.reply <-= dirgen(k.path & ~big 16r1F | big Qcredname, k.name, k);
				n.reply <-= (nil, nil);
			Qpkname =>
				k := findspkikeypath(n.path, nil);
				if(k == nil || k.pk == nil) {
					n.reply <-= (nil, Eremoved);
					break;
				}
				for(j := n.offset; --n.count >= 0 && j < len pkfiles; j++) {
					(ftype, name) := pkfiles[j];
					n.reply <-= dirgen((n.path & ~big 16r1F) | big ftype, name, k);
				}
				n.reply <-= (nil, nil);
			Qskname =>
				k := findspkikeypath(n.path, nil);
				if(k == nil || k.sk == nil) {
					n.reply <-= (nil, Eremoved);
					break;
				}
				for(j := n.offset; --n.count >= 0 && j < len skfiles; j++) {
					(ftype, name) := skfiles[j];
					n.reply <-= dirgen((n.path & ~big 16r1F) | big ftype, name, k);
				}
				n.reply <-= (nil, nil);
			Qcredname =>
				k := findspkikeypath(n.path, nil);
				if(k == nil) {
					n.reply <-= (nil, Eremoved);
					break;
				}

				if(k.cert != nil) {
					for(j := n.offset; --n.count >= 0 && j < len credcertfiles; j++) {
						(ftype, name) := credcertfiles[j];
						n.reply <-= dirgen((n.path & ~big 16r1F) | big ftype, name, k);
					}
				}
				if(k.pk != nil) {
					for(j := n.offset; --n.count >= 0 && j < len credpkfiles; j++) {
						(ftype, name) := credpkfiles[j];
						n.reply <-= dirgen((n.path & ~big 16r1F) | big ftype, name, k);
					}
				}
				if(k.sk != nil) {
					for(j := n.offset; --n.count >= 0 && j < len credskfiles; j++) {
						(ftype, name) := credskfiles[j];
						n.reply <-= dirgen((n.path & ~big 16r1F) | big ftype, name, k);
					}
				}
				n.reply <-= (nil, nil);
			}
		}
	}
}

timefd: ref Sys->FD;

time(): int
{
	if(timefd == nil){
		timefd = sys->open("/dev/time", Sys->OREAD);
		if(timefd == nil)
			return 0;
	}
	buf := array[128] of byte;
	sys->seek(timefd, big 0, 0);
	n := sys->read(timefd, buf, len buf);
	if(n < 0)
		return 0;
	t := (big string buf[0:n]) / big 1000000;
	return int t;
}

Checkpat: con "XXXXXXXXXXXXXXXX";       # it's what Plan 9's aescbc uses
Checklen: con len Checkpat;

Hdrlen: con 1+1+4;

packedsize(k: ref Spkikey): int
{
	s: int;

	s = 1 + len array of byte k.name;
	if(k.pk != nil)
		s += 4 + len array of byte k.pk.text();
	else
		s += 4;
	if(k.sk != nil)
		s += 4 + len array of byte k.sk.text();
	else
		s += 4;
	if(k.cert != nil)
		s += 4 + len array of byte k.cert.text();
	else
		s += 4;

	return s; 
}

pack(k: ref Spkikey): array of byte
{
	a := array[packedsize(k)] of byte;

	bn := array of byte k.name;
	n := len bn;
	if(n > 255)
		error(sys->sprint("overlong name: %s", k.name));
	a[0] = byte n;
	a[1:] = bn;

	n += 1;
	if(k.pk != nil) {
		bk := array of byte k.pk.text();
		m := len bk;
		a[n] = byte m;
		a[n + 1] = byte (m >> 8);
		a[n + 2] = byte (m >> 16);
		a[n + 3] = byte (m >> 24);

		n += 4;
		a[n:] = bk;
		n += m;
	}
	else {
		a[n] = byte 0;
		a[n + 1] = byte 0;
		a[n + 2] = byte 0;
		a[n + 3] = byte 0;

		n += 4;
	}

	if(k.sk != nil) {
		bk := array of byte k.sk.text();
		m := len bk;
		a[n] = byte m;
		a[n + 1] = byte (m >> 8);
		a[n + 2] = byte (m >> 16);
		a[n + 3] = byte (m >> 24);

		n += 4;
		a[n:] = bk;
		n += m;
	}
	else {
		a[n] = byte 0;
		a[n + 1] = byte 0;
		a[n + 2] = byte 0;
		a[n + 3] = byte 0;

		n += 4;
	}

	if(k.cert != nil) {
		bk := array of byte k.cert.text();
		m := len bk;
		a[n] = byte m;
		a[n + 1] = byte (m >> 8);
		a[n + 2] = byte (m >> 16);
		a[n + 3] = byte (m >> 24);

		n += 4;
		a[n:] = bk;
	}
	else {
		a[n] = byte 0;
		a[n + 1] = byte 0;
		a[n + 2] = byte 0;
		a[n + 3] = byte 0;
	}

	return a;
}

unpack(a: array of byte): (ref Spkikey, int)
{
	if(len a < 2)
		return (nil, 0);

	k := ref Spkikey;

	# Read the name
	n := int a[0];
	j := n + 1;
	if(j + 1 > len a)
		return (nil, 0);
	k.name = string a[1:j];

	# Read the public key, if there is one
	n = (int a[j + 3] << 24) | (int a[j + 2] << 16) | (int a[j + 1] << 8) | int a[j];
	j += 4;
	if(j + n > len a)
		return (nil, 0);
	if(n > 0) {
		(se, nil, msg) := Sexp.parse(string a[j:j + n]);
		if(msg != nil)
			return (nil, 0);
		k.pk = spki->parsekey(se);
	}
	j += n;
	if(j >= len a)
		return (nil, 0);

	# Read the secret key, if there is one
	n = (int a[j + 3] << 24) | (int a[j + 2] << 16) | (int a[j + 1] << 8) | int a[j];
	j += 4;
	if(j + n > len a)
		return (nil, 0);
	if(n > 0) {
		(se, nil, msg) := Sexp.parse(string a[j:j + n]);
		if(msg != nil)
			return (nil, 0);
		k.sk = spki->parsekey(se);
	}
	j += n;
	if(j >= len a)
		return (nil, 0);

	# Read the cert, if there is one
	n = (int a[j + 3] << 24) | (int a[j + 2] << 16) | (int a[j + 1] << 8) | int a[j];
	j += 4;
	if(j + n > len a)
		return (nil, 0);
	if(n > 0) {
		(se, nil, msg) := Sexp.parse(string a[j:j + n]);
		if(msg != nil)
			return (nil, 0);
		k.cert = spki->parsecert(se);
	}
	j += n;

	return (k, j);
}

corrupt(keyfile: string)
{
	fatal(sys->sprint("%s: incorrect key or corrupt/damaged keyfile", keyfile));
}

readkeys(keyfile: string)
{
	fd := sys->open(keyfile, Sys->OREAD);
	if(fd == nil) {
		error(sys->sprint("can't open %s: %r", keyfile));
		return;
	}

	(rc, d) := sys->fstat(fd);
	if(rc < 0)
		fatal(sys->sprint("can't get status of %s: %r", keyfile));

	length := int d.length;
	if(length == 0)
		return;
	if(length < AESbsize + Checklen)
		corrupt(keyfile);

	buf := array[length] of byte;
	if(sys->read(fd, buf, len buf) != len buf)
		fatal(sys->sprint("can't read %s: %r", keyfile));

	state := kr->aessetup(thekey, buf[0:AESbsize]);
	if(state == nil)
		fatal("can't initialize AES");

	kr->aescbc(state, buf[AESbsize:], length - AESbsize, Keyring->Decrypt);
	if(string buf[length - Checklen:] != Checkpat)
		corrupt(keyfile);

	length -= Checklen;
	for(i := AESbsize; i < length;) {
		(k, n) := unpack(buf[i:]);
		if(k == nil)
			corrupt(keyfile);
		newspkikey(k.name, nil, k);
		i += n;
	}
}

writekeys(keyfile: string)
{
	length := 0;
	for(i := 0; i < len keys; i++)
		if((k := keys[i]) != nil)
			length += packedsize(k);

	if(length == 0) {
		# leave it empty for clarity
		fd := sys->create(keyfile, Sys->OWRITE, 8r600);
		if(fd == nil)
			error(sys->sprint("can't create %s: %r", keyfile));
		return;
	}

	length += AESbsize + Checklen;
	buf := array[length] of byte;
	for(i = 0; i < AESbsize; i++)
		buf[i] = byte rand->rand(256);

	j := AESbsize;
	for(i = 0; i < len keys; i++) {
		if((k := keys[i]) != nil) {
			a := pack(k);
			buf[j:] = a;
			j += len a;
		}
	}

	buf[length - Checklen:] = array of byte Checkpat;
	state := kr->aessetup(thekey, buf[0:AESbsize]);
	if(state == nil)
		fatal("can't initialize AES");

	kr->aescbc(state, buf[AESbsize:], length - AESbsize, Keyring->Encrypt);

	fd := sys->create(keyfile, Sys->OWRITE, 8r600);
	if(fd == nil)
		error(sys->sprint("can't create %s: %r", keyfile));
	if(sys->write(fd, buf, len buf) != len buf)
		error(sys->sprint("error writing to %s: %r", keyfile));
}
