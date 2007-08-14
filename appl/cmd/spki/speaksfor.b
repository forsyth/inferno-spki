implement Speaksfor;

include "sys.m";
	sys: Sys;

include "draw.m";

include "keyring.m";
	kr: Keyring;

include "bufio.m";
	bufio: Bufio;
	Iobuf: import bufio;

include "sexprs.m";
	sexprs: Sexprs;
	Sexp: import sexprs;

include "spki.m";
	spki: SPKI;
	Key, Name, Cert, Valid, Subject, Seqel, Signature, Toplev: import spki;

include "arg.m";

Speaksfor: module
{
	init:	fn(nil: ref Draw->Context, nil: list of string);
};

init(nit: ref Draw->Context, args: list of string)
{
	sys = load Sys Sys->PATH;
	kr = load Keyring Keyring->PATH;
	bufio = load Bufio Bufio->PATH;
	sexprs = load Sexprs Sexprs->PATH;
	spki = load SPKI SPKI->PATH;

	arg := load Arg Arg->PATH;
	arg->init(args);
	arg->setusage("speaksfor [-k] -s subject -i issuer [-t tag] [-v valid]" 
			+ "[-p print cert] [-m keyfs mount point] keyfile");
	mountpoint := "/mnt/keys";
	certname: string = nil;
	subjectname: string = nil;
	issuername: string = nil;
	tagstr := "*";
	infkey := 0;
	printcert := 0;

	while((o := arg->opt()) != 0)
		case o {
		'c' =>
			certname = arg->earg();
		'i' =>
			issuername = arg->earg();
		'k' =>
			infkey = 1;
		'm' =>
			mountpoint = arg->earg();
		'p' =>
			printcert := 1;
		's' =>
			subjectname = arg->earg();
		't' =>
			tagstr = arg->earg();
		'v' =>
			;
		* =>
			arg->usage();
		}
	
	if(subjectname == nil || issuername == nil)
		arg->usage();

	if(certname == nil)
		certname = subjectname;
	
	args = arg->argv();
	if(args == nil)
		arg->usage();
	keyorfile := hd args;
	args = tl args;
	if(args != nil)
		arg->usage();
	arg = nil;

	sexprs->init();
	spki->init();

	# Read public and private keys of I
	ikey: ref Key;
	if(infkey){
		x := kr->readauthinfo(keyorfile);
		if(x == nil)
			error(sys->sprint("can't read authinfo from %s: %r", keyorfile));
		ikey = ref Key(x.mypk, x.mysk, 512, "md5", "pkcs1", nil);
	}
	else {
		ekey := readexpfile(keyorfile);
		ikey = spki->parsekey(ekey);
		if(ikey == nil)
			error(sys->sprint("can't parse key %s", keyorfile));
	}

	# Read public key of S
	spkexp := readexpfile(mountpoint + "/pk/" + subjectname + "/pubkey");
	
	# Construct certificate
	valid := ref Valid("0", "0");
	tag := ref Sexp.String(tagstr, nil);
	issuer := ref Name(ikey, nil);
	subject := ref Subject.P(spki->parsekey(spkexp));
	cert := ref Cert.A(nil, issuer, subject, valid, 1, tag);

	# Make signature
	(sig, err) := spki->signcert(cert, "rsa-pkcs1-md5", ikey);
	if(err != nil)
		error(err);

	# Make S-expression from certificate and signature
	seq := ref Seqel.C(cert) :: (ref Seqel.S(sig) :: nil);
	top := ref Toplev.Seq(seq);

	# Either print or add to keyfs
	if(printcert)
		sys->print("%s", top.text());
	else
		writefile(mountpoint + "/new", sys->sprint("%s = %s", certname, top.text()));
}

error(s: string)
{
	sys->fprint(sys->fildes(2), "speaksfor: %s\n", s);
	raise "fail:error";
}

writefile(name: string, s: string)
{
	fd := bufio->open(name, Bufio->OWRITE);
	if(fd == nil)
		error(sys->sprint("can't open %s: %r", name));

	if(fd.write(array of byte s, len s) < len s)
		error(sys->sprint("can't write to %s: %r", name));

	return;
}

readexpfile(name: string): ref Sexp
{
	fd := bufio->open(name, Bufio->OREAD);
	if(fd == nil)
		error(sys->sprint("can't open %s: %r", name));

	(exp, err) := Sexp.read(fd);
	if(err != nil)
		error(sys->sprint("invalid s-expression: %s", err));

	return exp;
}
