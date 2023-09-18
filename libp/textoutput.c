/* --------------------------------------------------- */
/* | Copyright (c) 1986 MIPS Computer Systems, Inc.  | */
/* | All Rights Reserved.                            | */
/* --------------------------------------------------- */
/* $Header: textoutput.c,v 1030.6 88/03/02 13:45:42 bettina Exp $ */

/* Pascal text output routines. */
#include "pascalio.h"

/* Internal routine for putting a string into an output buffer. */
/* Writes directly into stdio package's buffer for efficiency. */
/* Note: this is equivalent to fwrite, and should probably be changed
   to be fwrite (it is a lot more efficient than fwrite). */
private void
write_chars (f, s, n)
     register FILE *f;
     register unsigned char *s;
     register unsigned n;
{
    register unsigned char *d, *e;
    if (!(f->_flag & _IOWRT)) return;
    while ((f->_cnt -= n) < 0) {
	/* Not enough room in buffer for whole string.  Fill rest of buffer,
	   output the buffer, and then try again. */
	f->_cnt += n;
	if (f->_cnt > 0) {
	    n -= f->_cnt;
	    e = s+f->_cnt;
	    d = f->_ptr;
	    /* memcpy? */
	    do {
		*d++ = *s++;
	    } while (s != e);
	    f->_ptr = d;
	}
	f->_cnt = -1;
	_flsbuf(*s++, f);
	n -= 1;
	if (n == 0) return;
    }
    /* Output now fits in buffer. */
    e = s+n;
    d = f->_ptr;
    /* memcpy? */
    do {
	*d++ = *s++;
    } while (s != e);
    f->_ptr = d;
}

/* Internal routine for putting N spaces into an output buffer. */
/* Writes directly into stdio package's buffer for efficiency. */
private void
pad (f, c, n)
     register FILE *f;
     register int n;
{
    register unsigned char *d, *e;
    if (!(f->_flag & _IOWRT)) return;
    if (n <= 0) return;
    while ((f->_cnt -= n) < 0) {
	/* Not enough room in buffer for whole string.  Fill rest of buffer,
	   output the buffer, and then try again. */
	f->_cnt += n;
	if (f->_cnt > 0) {
	    n -= f->_cnt;
	    d = f->_ptr;
	    e = d+f->_cnt;
	    /* memset? */
	    do {
		*d++ = c;
	    } while (d != e);
	    f->_ptr = d;
	}
	f->_cnt = -1;
	_flsbuf(c, f);
	n -= 1;
	if (n == 0) return;
    }
    /* Output now fits in buffer. */
    d = f->_ptr;
    e = d+n;
    /* memset? */
    do {
	*d++ = c;
    } while (d != e);
    f->_ptr = d;
}

/* Pascal-called routine to output a NL. */
void
writeln (f)
     register FILE *f;
{
    if (!(f->_flag & _IOWRT)) {
	fprintf(stderr, "writeln called on file not open for writing.\n");
	return;
    }
    putc ('\n', f);
}

/* Pascal-called routine to output a ^L. */
void
page (f)
     register FILE *f;
{
    putc ('\014', f);
}

/* Pascal-called routine to output a character. */
void
write_char (f, c, width)
     register FILE *f;
     register unsigned char c;
     register int width;
{
    if (width > 1) {
	pad (f, ' ', width - 1);
	putc (c, f);
    }
    else if (width < -1) {
	putc (c, f);
	pad (f, ' ', (-width) - 1);
    }
    else {
	putc (c, f);
    }
}

/* Pascal-called routine to output a string. */
void
write_string (f, s, length, width)
     register FILE *f;
     register unsigned char *s;
     register unsigned length;
     register int width;
{
    if (width == 0) {		/* trim blanks from end */
	register unsigned char *e = s + length;
	/* Want inner loop to be: (but...)
	   L1:	BNE E,S,L3
		 SUB E,1
		BEQ T0,T1,L1
		 LBU T0,(E)
	   L2:	...
	   L3:	BNE T0,T1,L2
	   */
	while (e != s && e[-1] == ' ') e -= 1;
	width = e - s;
    }
    else if (width > length) {
	pad (f, ' ', width - length);
        width = length;
    }
    if (width > 0) {
	write_chars (f, s, width);
    }
}

/* Pascal-called routine to output an enum . */
void
write_enum(f, e, s, w, b)
     register FILE *f;
     register unsigned e;
     register unsigned char *s;
     register long w;
              long b;
{
    register long e1 = e;

    while (e > 0)
      {
      while (*s++ != '\0');
      if (*s == '\0') 
	{
	fprintf(stderr, "Enumerated value '%d' not within type.\n", e1);
	return;
	}
      e--;
      }
    if (*s == ' ') {
	while (*s++ == ' ');
	s--;
    }
    write_string(f, s, strlen(s), w);
}

private unsigned char digits[36+1] = "0123456789abcdefghijklmnopqrstuvwxyz";

/* Pascal-called routine to output an integer. */
void
write_integer (f, i, width, radix)
     register FILE *f;
     register int i;
     register int width;
     register unsigned radix;
{
#define BUFLEN 33
    unsigned char buffer[BUFLEN];
    register unsigned char *k;
    register unsigned n;

    if (radix <= 0) {
	fprintf(stderr, "illegal radix specified for integer write: %d\n", radix);
	return;
    }

    n = i < 0 ? -i : i;
    k = &buffer[BUFLEN];
    do {
	*--k = digits[n % radix];
	n = n / radix;
    } while (n != 0);
    if (i < 0) {
	*--k = '-';
    }
    n = &buffer[BUFLEN] - k;
    if (width > (int)n) {
	pad (f, ' ', width - n);
    }
    write_chars (f, k, n);
    if ((-width) > (int)n) {
	pad (f, ' ', (-width) - n);
    }
#undef BUFLEN
}

/* Pascal-called routine to output an unsigned integer. */
void
write_cardinal (f, n, width, radix)
     register FILE *f;
     register unsigned n;
     register int width;
     register unsigned radix;
{
#define BUFLEN 32
    unsigned char buffer[BUFLEN];
    register unsigned char *k;

    if (radix <= 0) {
	fprintf(stderr, "illegal radix specified for cardinal write: %d\n", radix);
	return;
    }
    k = &buffer[BUFLEN];
    do {
	*--k = digits[n % radix];
	n = n / radix;
    } while (n != 0);
    n = &buffer[BUFLEN] - k;
    if (width > (int)n) {
	pad (f, ' ', width - n);
    }
    write_chars (f, k, n);
    if ((-width) > (int)n) {
	pad (f, ' ', (-width) - n);
    }
#undef BUFLEN
}

extern unsigned char *ecvt(), *fcvt();

/* Pascal-called routine to output a single-precision float. */
void
write_real (f, r, width, precision)
     register FILE *f;
     union {int i; float f} r;		/* KLUDGE to get a float argument */
     register int width;
     register int precision;
{
#define ExpDigits 2
    int exp, sign;
    int ndigit;
    register unsigned char *p, *e;

    if (precision <= 0) {
	/* ISO floating point format */

	ndigit = max(width-ExpDigits-4, 2);
	if (r.f == 0.0) {
	    write_chars (f, " 0.", 3);
	    pad (f, '0', ndigit - 1);
	    write_chars (f, "e+000", 2+ExpDigits);
	} else {
	    p = ecvt(r.f, ndigit, &exp, &sign);
	    if (p[0] == 'I' || p[0] == 'N') {
		ndigit = strlen(p);
		pad (f, ' ', width - ndigit);
		write_chars (f, p, ndigit);
	    }
	    else {
		exp -= 1;
		putc (sign ? '-' : ' ', f);
		putc (*p++, f);
		putc ('.', f);
		write_chars (f, p, ndigit-1);
		putc ('e', f);
		putc (exp < 0 ? (exp = -exp, '-') : '+', f);
		putc ('0' + (exp / 10), f);
		putc ('0' + (exp % 10), f);
	    }
	}
    } else {
	/* ISO fixed-point format */
	p = fcvt(r.f, precision, &exp, &sign);
	ndigit = strlen (p);
	sign = (sign != 0);
	if (exp <= 0) {
	    register unsigned zpad;
	    if (width - (sign + 2 + precision) > 0) {
		pad (f, ' ', width - (sign + 2 + precision));
	    }
	    if (sign) putc('-', f);
	    putc ('0', f);
	    putc ('.', f);
	    exp = - exp;
	    zpad = precision;
	    if (exp < precision) {
		pad (f, '0', exp);
		zpad -= exp;
		if (ndigit > zpad) ndigit = zpad;
		write_chars (f, p, ndigit);
		zpad -= ndigit;
	    }
	    pad (f, '0', zpad);
	    if ((-width) - (sign + 2 + precision) > 0) {
		pad (f, ' ', (-width) - (sign + 2 + precision));
	    }
	} else {
	    if (width - (sign + exp + 1 + precision) > 0) {
		pad (f, ' ', width - (sign + exp + 1 + precision));
	    }
	    if (sign) putc('-', f);
	    if (exp >= ndigit) {
		write_chars (f, p, ndigit);
		pad (f, '0', exp-ndigit);
		putc ('.', f);
		pad (f, '0', precision);
	    } else {
		write_chars (f, p, exp);
		p += exp;
		ndigit -= exp;
		putc ('.', f);
		if (precision <= ndigit) {
		    write_chars (f, p, precision);
		} else {
		    write_chars (f, p, ndigit);
		    pad (f, '0', precision - ndigit);
		}
	    }
	    if ((-width) - (sign + exp + 1 + precision) > 0) {
		pad (f, ' ', (-width) - (sign + exp + 1 + precision));
	    }
	}
    }
#undef ExpDigits
}

/* Pascal-called routine to output a double-precision float. */
void
write_double (f, d, width, precision)
     register FILE *f;
     double d;
     register int width;
     register int precision;
{
#define ExpDigits 3
    int exp, sign;
    int ndigit;
    register unsigned char *p, *e;

    if (precision <= 0) {
	/* ISO floating point format */

	ndigit = max(width-ExpDigits-4, 2);
	if (d == 0.0) {
	    write_chars (f, " 0.", 3);
	    pad (f, '0', ndigit - 1);
	    write_chars (f, "e+000", 2+ExpDigits);
	} else {
	    p = ecvt(d, ndigit, &exp, &sign);
	    if (p[0] == 'I' || p[0] == 'N') {
		ndigit = strlen(p);
		pad (f, ' ', width - ndigit);
		write_chars (f, p, ndigit);
	    }
	    else {
		exp -= 1;
		putc (sign ? '-' : ' ', f);
		putc (*p++, f);
		putc ('.', f);
		write_chars (f, p, ndigit-1);
		putc ('e', f);
		putc (exp < 0 ? (exp = -exp, '-') : '+', f);
		putc ('0' + (exp / 100), f);
		exp %= 100;
		putc ('0' + (exp / 10), f);
		putc ('0' + (exp % 10), f);
	    }
	}
    } else {
	/* ISO fixed-point format */
	p = fcvt(d, precision, &exp, &sign);
	ndigit = strlen (p);
	sign = (sign != 0);
	if (exp <= 0) {
	    register unsigned zpad;
	    if (width - (sign + 2 + precision) > 0) {
		pad (f, ' ', width - (sign + 2 + precision));
	    }
	    if (sign) putc('-', f);
	    putc ('0', f);
	    putc ('.', f);
	    exp = - exp;
	    zpad = precision;
	    if (exp < precision) {
		pad (f, '0', exp);
		zpad -= exp;
		if (ndigit > zpad) ndigit = zpad;
		write_chars (f, p, ndigit);
		zpad -= ndigit;
	    }
	    pad (f, '0', zpad);
	    if ((-width) - (sign + 2 + precision) > 0) {
		pad (f, ' ', (-width) - (sign + 2 + precision));
	    }
	} else {
	    pad (f, ' ', width - (sign + exp + 1 + precision));
	    if (sign) putc('-', f);
	    if (exp >= ndigit) {
		write_chars (f, p, ndigit);
		pad (f, '0', exp-ndigit);
		putc ('.', f);
		pad (f, '0', precision);
	    } else {
		write_chars (f, p, exp);
		p += exp;
		ndigit -= exp;
		putc ('.', f);
		if (precision <= ndigit) {
		    write_chars (f, p, precision);
		} else {
		    write_chars (f, p, ndigit);
		    pad (f, '0', precision - ndigit);
		}
	    }
	    if ((-width) - (sign + exp + 1 + precision) > 0) {
		pad (f, ' ', (-width) - (sign + exp + 1 + precision));
	    }
	}
    }
#undef ExpDigits
}

/* Pascal-called routine to output a boolean. */
void
write_boolean (f, b, width)
     register FILE *f;
     register unsigned b;
     register int width;
{
    if (b) {
	if (width > 4) {
	    pad (f, ' ', width - 4);
	}
	write_chars (f, "true", 4);
	if ((-width) > 4) {
	    pad (f, ' ', (-width) - 4);
	}
    } else {
	if (width > 5) {
	    pad (f, ' ', width - 5);
	}
	write_chars (f, "false", 5);
	if ((-width) > 5) {
	    pad (f, ' ', (-width) - 5);
	}
    }
}
