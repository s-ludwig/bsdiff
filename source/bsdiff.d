/* ported from https://github.com/mendsley/bsdiff
*/
module bsdiff;

import std.experimental.allocator : theAllocator, makeArray, dispose;
import std.exception : enforce;

void bsdiff(Allocator)(in ubyte[] old, in ubyte[] new_, scope void delegate(in ubyte[]) write, Allocator allocator = theAllocator)
{
	auto I = allocator.makeArray!long(old.length + 1);
	scope (exit) allocator.dispose(I);
	auto buffer = allocator.makeArray!ubyte(new_.length + 1);
	scope (exit) allocator.dispose(buffer);

	qsufsort(I, old, allocator);

	/* Compute the differences, writing ctrl as we go */
	long scan = 0;
	long len = 0;
	long pos = 0;
	long lastscan = 0;
	long lastpos = 0;
	long lastoffset = 0;
	while (scan < new_.length) {
		long oldscore = 0;

		for (long scsc = scan+=len; scan < new_.length; scan++) {
			len = search(I, old,new_[scan .. $], 0, old.length, &pos);

			for (; scsc < scan+len; scsc++)
				if ((scsc+lastoffset < old.length) && (old[scsc+lastoffset] == new_[scsc]))
					oldscore++;

			if (((len==oldscore) && (len!=0)) || (len>oldscore+8))
				break;

			if ((scan+lastoffset<old.length) && (old[scan+lastoffset] == new_[scan]))
				oldscore--;
		}

		if ((len != oldscore) || (scan == new_.length)) {
			long s = 0;
			long Sf = 0;
			long lenf = 0;
			for (long i = 0; (lastscan+i < scan) && (lastpos+i < old.length);) {
				if (old[lastpos+i] == new_[lastscan+i]) s++;
				i++;
				if (s*2-i > Sf*2-lenf) {
					Sf = s;
					lenf = i;
				}
			}

			long lenb = 0;
			if (scan < new_.length) {
				s = 0;
				long Sb = 0;
				for (long i = 1; (scan>=lastscan+i)&&(pos>=i); i++) {
					if (old[pos-i] == new_[scan-i]) s++;
					if (s*2-i > Sb*2-lenb) {
						Sb=s;
						lenb=i;
					}
				}
			}

			if (lastscan+lenf > scan-lenb) {
				long overlap = (lastscan+lenf)-(scan-lenb);
				s = 0;
				long Ss = 0;
				long lens = 0;
				foreach (i; 0 .. overlap) {
					if (new_[lastscan+lenf-overlap+i] == old[lastpos+lenf-overlap+i])
						s++;
					if (new_[scan-lenb+i] == old[pos-lenb+i])
						s--;
					if (s > Ss) {
						Ss = s;
						lens = i+1;
					}
				}

				lenf += lens-overlap;
				lenb -= lens;
			}

			ubyte[3 * 8] buf;
			offtout(lenf, buf);
			offtout((scan-lenb)-(lastscan+lenf), buf[8 .. $]);
			offtout((pos-lenb)-(lastpos+lenf), buf[16 .. $]);

			/* Write control data */
			write(buf);

			/* Write diff data */
			if (lenf) {
				buffer[0 .. lenf] = new_[lastscan .. lastscan+lenf] - old[lastpos .. lastpos+lenf];
				write(buffer[0 .. lenf]);
			}

			/* Write extra data */
			if (scan-lenb > lastscan+lenf)
				write(new_[lastscan+lenf .. scan-lenb]);

			lastscan = scan-lenb;
			lastpos = pos-lenb;
			lastoffset = pos-scan;
		}
	}
}


void bspatch(in ubyte[] old, ubyte[] new_, scope void delegate(ubyte[]) read)
{
	ubyte[8] buf;
	long oldpos = 0, newpos = 0;
	long[3] ctrl;

	while (newpos < new_.length) {
		/* Read control data */
		foreach (i; 0 .. 3) {
			read(buf);
			ctrl[i] = offtin(buf);
		}

		/* Sanity-check */
		enforce(newpos + ctrl[0] < new_.length);

		/* Read diff string */
		read(new_[newpos .. newpos + ctrl[0]]);

		/* Add old data to diff string */
		foreach (i; 0 .. ctrl[0])
			if ((oldpos+i>=0) && (oldpos+i<old.length))
				new_[newpos+i] += old[oldpos+i];

		/* Adjust pointers */
		newpos += ctrl[0];
		oldpos += ctrl[0];

		/* Sanity-check */
		enforce(newpos+ctrl[1] <= new_.length);

		/* Read extra string */
		if (ctrl[1] > 0)
			read(new_[newpos .. newpos + ctrl[1]]);

		/* Adjust pointers */
		newpos += ctrl[1];
		oldpos += ctrl[2];
	}
}

unittest {
	ubyte[] a = [1, 2, 3, 4, 5, 6, 7, 8];
	ubyte[] b = [2, 3, 4, 5, 13, 14, 15, 16, 7];
	ubyte[] patch;
	void writePatch(in ubyte[] bts) {
		patch ~= bts;
	}
	void readPatch(ubyte[] dst) {
		dst[] = patch[0 .. dst.length];
		patch = patch[dst.length .. $];
	}

	bsdiff(a, b, &writePatch);
	ubyte[] c = new ubyte[](b.length);
	bspatch(a, c, &readPatch);
	assert(b == c);
}


private void split(long[] I, long[] V, long start, long len, long h)
{
	import std.algorithm.mutation : swap;

	long x;

	if (len < 16) {
		long j;
		for (long k = start; k < start+len; k += j) {
			j = 1;
			x = V[I[k]+h];
			for (long i = 1; k+i < start+len; i++) {
				if (V[I[k+i]+h] < x) {
					x = V[I[k+i]+h];
					j = 0;
				}
				if (V[I[k+i]+h] == x) {
					swap(I[k+i], I[k+j]);
					j++;
				}
			}
			foreach (i; 0 .. j) V[I[k+i]] = k+j-1;
			if (j == 1) I[k]=-1;
		}
		return;
	}

	x = V[I[start+len/2]+h];
	long jj = 0;
	long kk = 0;
	foreach (i; start .. start+len) {
		if (V[I[i]+h] < x) jj++;
		if (V[I[i]+h] == x) kk++;
	}
	jj += start;
	kk += jj;

	long i = start;
	long j = 0;
	long k = 0;
	while (i < jj) {
		if (V[I[i]+h] < x) {
			i++;
		} else if (V[I[i]+h] == x) {
			swap(I[i], I[jj+j]);
			j++;
		} else {
			swap(I[i], I[kk+k]);
			k++;
		}
	}

	while (jj+j < kk) {
		if (V[I[jj+j]+h] == x) {
			j++;
		} else {
			swap(I[jj+j], I[kk+k]);
			k++;
		}
	}

	if (jj > start) split(I, V, start, jj-start, h);

	foreach (i2; 0 .. kk-jj) V[I[jj+i2]] = kk-1;
	if (jj == kk-1) I[jj] = -1;

	if (start+len > kk) split(I, V, kk, start+len-kk, h);
}

private void qsufsort(Allocator)(long[] I, const(ubyte)[] old, Allocator allocator)
{
	long[] V = allocator.makeArray!long(old.length+1);
	allocator.dispose(V);

	long[256] buckets = 0;

	foreach (i; 0 .. old.length) buckets[old[i]]++;
	foreach (i; 1 .. buckets.length) buckets[i] += buckets[i-1];
	foreach_reverse (i; 1 .. buckets.length) buckets[i] = buckets[i-1];
	buckets[0] =0 ;

	foreach (i; 0 .. old.length) I[++buckets[old[i]]] = i;
	I[0] = old.length;
	foreach (i; 0 .. old.length) V[i] = buckets[old[i]];
	V[old.length] = 0;
	foreach (i; 1 .. buckets.length)
		if (buckets[i] == buckets[i-1]+1)
			I[buckets[i]] = -1;
	I[0] = -1;

	for (long h = 1; I[0] != -(old.length+1); h += h) {
		long len = 0;
		long i = 0;
		while (i < old.length+1) {
			if (I[i] < 0) {
				len -= I[i];
				i -= I[i];
			} else {
				if (len) I[i-len] = -len;
				len = V[I[i]] + 1 - i;
				split(I, V, i, len, h);
				i += len;
				len = 0;
			}
		}
		if (len) I[i-len] = -len;
	}

	foreach (i; 0 .. old.length+1) I[V[i]] = i;
}

private long matchlen(const(ubyte)[] old, const(ubyte)[] new_)
{
	import std.algorithm.comparison : min;
	auto len = min(old.length, new_.length);

	foreach (i; 0 .. len)
		if (old[i] != new_[i])
			return i;

	return len;
}

private long search(in long[] I, in ubyte[] old,
		in ubyte[] new_, long st, long en, long *pos)
{
	import core.stdc.string : memcmp;
	import std.algorithm.comparison : min;

	if (en-st < 2) {
		auto x = matchlen(old[I[st] .. $], new_);
		auto y = matchlen(old[I[en] .. $], new_);

		if (x > y) {
			*pos = I[st];
			return x;
		} else {
			*pos = I[en];
			return y;
		}
	}

	long x = st + (en-st)/2;
	if (memcmp(&old[I[x]], &new_[0], min(old.length-I[x], new_.length)) < 0) {
		return search(I, old, new_, x, en, pos);
	} else {
		return search(I, old, new_, st, x, pos);
	}
}

struct bsdiff_request
{
	const(ubyte)[] old;
	const(ubyte)[] new_;
	void delegate(in ubyte[] data) write;
	long[] I;
	ubyte[] buffer;
};


private long offtin(in ubyte[] buf)
{
	long y = buf[7]&0x7F;
	y = y*256; y+= buf[6];
	y = y*256; y+= buf[5];
	y = y*256; y+= buf[4];
	y = y*256; y+= buf[3];
	y = y*256; y+= buf[2];
	y = y*256; y+= buf[1];
	y = y*256; y+= buf[0];
	return buf[7] & 0x80 ? -y : y;
}


private void offtout(long x, ubyte[] buf)
{
	ulong y = x < 0 ? -x : x;
	buf[0] = y%256; y -= buf[0];
	y = y/256; buf[1] = y%256; y -= buf[1];
	y = y/256; buf[2] = y%256; y -= buf[2];
	y = y/256; buf[3] = y%256; y -= buf[3];
	y = y/256; buf[4] = y%256; y -= buf[4];
	y = y/256; buf[5] = y%256; y -= buf[5];
	y = y/256; buf[6] = y%256; y -= buf[6];
	y = y/256; buf[7] = y%256;
	if (x < 0) buf[7] |= 0x80;
}
