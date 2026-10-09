#!/usr/bin/env python3
"""Exact finite checks for ob-lean (Barker sequences of odd length).

Standard library only, exact integers, no `assert` (python -O cannot strip a check).  One process.
Every failed check prints a FAIL line; the last line is `VERDICT: PASS` or `VERDICT: FAIL`, and the
exit status is 0 only on PASS.

  1. Every +-1 sequence of length n, 1 <= n <= 45, that is Barker, by an outside-in backtracking
     search (fixing the outer entries settles the long shifts first); each sequence found is
     re-checked by a plain recomputation of every autocorrelation; for n <= 16 the sets found are
     compared with a plain enumeration of all 2^n sequences.  Expected: lengths
     {1, 2, 3, 4, 5, 7, 11, 13} with 2, 4, 4, 8, 4, 4, 4, 4 sequences.
  2. On every odd Barker sequence found, the structure statements of Challenge.lean as written:
     aperiodic_eq, skew, fold, doubling, run_bounds (the last by enumerating every pair (p, q)
     meeting its hypotheses literally, with natural-number subtraction and divisibility).
  3. On every even Barker sequence of length > 2: 4 | n, the periodic autocorrelations vanish off
     the peak, and the circulant matrix H[i][j] = h[(j - i) mod n] has H H^T = n I.
  4. Forged controls: +++++--++-+-- has C(1) = 2 and is rejected; every single-sign flip of every
     odd Barker sequence is classified, and the structure checks must fail on every flip that is not
     Barker (each of aperiodic_eq, skew, fold, doubling must fail somewhere, and run_bounds on a
     planted sequence), so the checks can fail.
  5. The abstraction check: for odd n <= 61, +-1 sequences satisfying only skew and fold (no Barker
     hypothesis) exist only at n in {1, 3, 5, 7, 11, 13}; a DFS capped at 120 s that prints UNKNOWN
     rather than claiming if the cap is hit.

This is a check of the finite cases and of the statements on them, not a proof of the theorem.
The skew + fold sequences at those lengths are also compared with the Barker sequences found in 1.
Usage: python3 scripts/check_barker.py [--kill-file PATH]   (the run stops if PATH exists)
"""

import itertools
import os
import sys
import time

NMAX = 45
CROSS_MAX = 16
ABS_MAX = 61
ABS_CAP_S = 120.0
EXPECTED = {1: 2, 2: 4, 3: 4, 4: 8, 5: 4, 7: 4, 11: 4, 13: 4}
ODD_LENGTHS = [1, 3, 5, 7, 11, 13]

# the eight witnesses of OB/Witnesses.lean and its forged control
WITNESSES = {
    1: (1,),
    2: (1, 1),
    3: (1, 1, -1),
    4: (1, 1, 1, -1),
    5: (1, 1, 1, -1, 1),
    7: (1, 1, 1, -1, -1, 1, -1),
    11: (1, 1, 1, -1, -1, -1, 1, -1, -1, 1, -1),
    13: (1, 1, 1, 1, 1, -1, -1, 1, 1, -1, 1, -1, 1),
}
FORGED13 = "+++++--++-+--"

failures = []
KILL_FILE = None


def fail(msg):
    failures.append(msg)
    print("FAIL: " + msg)


class Killed(Exception):
    pass


def check_kill():
    if KILL_FILE is not None and os.path.exists(KILL_FILE):
        raise Killed()


def fmt(h):
    return "".join("+" if x == 1 else "-" for x in h)


def parse(s):
    return tuple(1 if c == "+" else -1 for c in s)


# ---------------------------------------------------------------- plain definitions

def aperiodic(h, k):
    """C(k) = sum_{j < n-k} h[j] h[j+k] (the definition of Challenge.lean; 0 for k >= n)."""
    n = len(h)
    return sum(h[j] * h[j + k] for j in range(max(n - k, 0)))


def is_barker_plain(h):
    if any(x != 1 and x != -1 for x in h):
        return False
    n = len(h)
    return all(abs(aperiodic(h, k)) <= 1 for k in range(1, n))


def periodic(h, u):
    n = len(h)
    return sum(h[j] * h[(j + u) % n] for j in range(n))


def npow(e):
    """(-1)^e for a natural number e."""
    return -1 if e % 2 else 1


def nsub(a, b):
    """truncated natural subtraction, as in Lean's Nat."""
    return a - b if a >= b else 0


def ndvd(a, b):
    """a | b in Lean's Nat: 0 | b iff b = 0."""
    return b == 0 if a == 0 else b % a == 0


# ---------------------------------------------------------------- 1. the search

def search_outside_in(n, counter):
    """All Barker sequences of length n.  Level k fixes positions k and n-1-k; then the shift
    n-1-k is fully determined (its pairs are (i, i+n-1-k), i <= k) and is checked at once."""
    h = [0] * n
    out = []

    def leaf():
        # the shifts n-1-k for every level were checked on the way down; check the rest here
        for s in range(1, n):
            c = 0
            for j in range(n - s):
                c += h[j] * h[j + s]
            if c > 1 or c < -1:
                return
        out.append(tuple(h))

    def rec(k):
        counter[0] += 1
        if (counter[0] & 0xFFFF) == 0:
            check_kill()
        lo, hi = k, n - 1 - k
        if lo > hi:
            leaf()
            return
        if lo == hi:
            for a in (1, -1):
                h[lo] = a
                leaf()
            h[lo] = 0
            return
        for a in (1, -1):
            h[lo] = a
            for b in (1, -1):
                h[hi] = b
                c = 0
                for i in range(k + 1):
                    c += h[i] * h[i + hi]
                if -1 <= c <= 1:
                    rec(k + 1)
            h[hi] = 0
        h[lo] = 0

    rec(0)
    return out


def search_plain(n):
    return [t for t in itertools.product((1, -1), repeat=n) if is_barker_plain(t)]


# ---------------------------------------------------------------- 2. structure statements

def run_pairs(h):
    """Every (p, q) meeting the hypotheses of run_bounds, read literally."""
    n = len(h)
    pairs = []
    for p in range(n):
        if h[p] == h[nsub(p, 1)]:
            continue
        if not all(h[s] == h[s - 1] for s in range(1, p)):
            continue
        for q in range(n):
            if h[q] == h[nsub(q, 1)] or ndvd(p, q):
                continue
            if all(ndvd(p, s) for s in range(1, q) if h[s] != h[s - 1]):
                pairs.append((p, q))
    return pairs


def structure_failures(h):
    """Names of the structure statements of Challenge.lean that fail on h (odd n)."""
    n = len(h)
    m = (n - 1) // 2
    bad = set()
    for k in range(1, n):
        want = npow(m) if k % 2 == 0 else 0
        if aperiodic(h, k) != want:
            bad.add("aperiodic_eq")
    for k in range(n):
        if h[k] * h[n - 1 - k] != npow(m + k):
            bad.add("skew")
    for w in range(0, n, 2):
        if w + 3 <= n and sum(npow(k) * h[k] * h[w - k] for k in range(w + 1)) != 1:
            bad.add("fold")
    for u in range(1, n):
        if 2 * u + 3 <= n and h[u - 1] * h[u] != h[2 * u - 1] * h[2 * u]:
            bad.add("doubling")
    if n >= 7 and h[0] == h[1]:
        for p, q in run_pairs(h):
            if not (p % 2 == 1 and q % 2 == 1 and 2 * q <= n + 3 and n <= p + q + 1):
                bad.add("run_bounds")
    return bad


# ---------------------------------------------------------------- 5. abstraction DFS

class Timeout(Exception):
    pass


def skew_fold_exists(n, deadline, counter):
    """Is there a +-1 sequence of odd length n satisfying skew and fold (as in Challenge.lean)?
    Positions are assigned in order; position j > m is forced by skew from position n-1-j; the fold
    at even w <= n-3 uses positions 0..w only and is checked as soon as w is assigned."""
    m = (n - 1) // 2
    h = [0] * n
    out = []

    def full_check():
        for k in range(n):
            if h[k] * h[n - 1 - k] != npow(m + k):
                return False
        for w in range(0, n - 2, 2):
            if sum(npow(k) * h[k] * h[w - k] for k in range(w + 1)) != 1:
                return False
        return True

    def rec(j):
        counter[0] += 1
        if (counter[0] & 0x3FFF) == 0:
            check_kill()
            if time.monotonic() > deadline:
                raise Timeout()
        if j == n:
            if full_check():
                out.append(tuple(h))
            return
        if j <= m:
            choices = (1, -1)
        else:
            choices = (npow(m + (n - 1 - j)) * h[n - 1 - j],)
        for x in choices:
            h[j] = x
            if j == m and h[m] * h[n - 1 - m] != npow(m + m):
                continue
            if j % 2 == 0 and j + 3 <= n:
                if sum(npow(k) * h[k] * h[j - k] for k in range(j + 1)) != 1:
                    continue
            rec(j + 1)
        h[j] = 0

    rec(0)
    return out


# ---------------------------------------------------------------- main

def main():
    global KILL_FILE
    args = sys.argv[1:]
    if args[:1] == ["--kill-file"] and len(args) == 2:
        KILL_FILE = args[1]
    elif args:
        print("usage: check_barker.py [--kill-file PATH]")
        return 2
    t_all = time.monotonic()
    print("check_barker.py: python %s" % sys.version.split()[0])

    # 1 ------------------------------------------------------------------------------
    t = time.monotonic()
    found = {}
    nodes = [0]
    for n in range(1, NMAX + 1):
        check_kill()
        seqs = search_outside_in(n, nodes)
        for s in seqs:
            if not is_barker_plain(s):
                fail("n=%d: search returned %s, rejected by the plain recomputation" % (n, fmt(s)))
        if len(set(seqs)) != len(seqs):
            fail("n=%d: duplicate sequences in the search output" % n)
        if seqs:
            found[n] = sorted(set(seqs))
    counts = {n: len(v) for n, v in found.items()}
    print("1. outside-in search, 1 <= n <= %d: %d nodes, %.1f s" % (NMAX, nodes[0], time.monotonic() - t))
    print("   Barker lengths and counts: %s" % counts)
    if counts != EXPECTED:
        fail("lengths/counts %s differ from the expected %s" % (counts, EXPECTED))
    for n in sorted(found):
        print("   n=%2d: %s" % (n, " ".join(fmt(s) for s in found[n])))
    for n, w in WITNESSES.items():
        if w not in found.get(n, []):
            fail("the Lean witness of length %d (%s) is not among the sequences found" % (n, fmt(w)))
    t = time.monotonic()
    for n in range(1, CROSS_MAX + 1):
        check_kill()
        plain = sorted(search_plain(n))
        if plain != found.get(n, []):
            fail("n=%d: plain 2^n enumeration finds %d sequences, the search %d"
                 % (n, len(plain), len(found.get(n, []))))
    print("1b. plain 2^n enumeration for n <= %d agrees with the search set by set: %s (%.1f s)"
          % (CROSS_MAX, "yes" if not any("plain 2^n" in f for f in failures) else "NO",
             time.monotonic() - t))

    # 2 ------------------------------------------------------------------------------
    t = time.monotonic()
    nseq = 0
    for n in sorted(found):
        if n % 2 == 0:
            continue
        for h in found[n]:
            nseq += 1
            bad = structure_failures(h)
            if bad:
                fail("n=%d %s: structure statements fail: %s" % (n, fmt(h), sorted(bad)))
            if n >= 7 and h[0] == h[1]:
                pairs = run_pairs(h)
                if len(pairs) != 1:
                    fail("n=%d %s: %d pairs (p, q) meet the run_bounds hypotheses, expected 1"
                         % (n, fmt(h), len(pairs)))
                for p, q in pairs:
                    print("   run_bounds n=%2d %s: p=%d q=%d, p q odd, 2q=%d <= n+3=%d, n <= p+q+1=%d"
                          % (n, fmt(h), p, q, 2 * q, n + 3, p + q + 1))
    print("2. aperiodic_eq, skew, fold, doubling, run_bounds on all %d odd Barker sequences (%.2f s)"
          % (nseq, time.monotonic() - t))

    # 3 ------------------------------------------------------------------------------
    neven = 0
    for n in sorted(found):
        if n % 2 == 1 or n <= 2:
            continue
        for h in found[n]:
            neven += 1
            if n % 4 != 0:
                fail("even Barker n=%d %s: 4 does not divide n" % (n, fmt(h)))
            per = [periodic(h, u) for u in range(n)]
            if per[0] != n or any(per[u] != 0 for u in range(1, n)):
                fail("even Barker n=%d %s: periodic autocorrelations %s" % (n, fmt(h), per))
            H = [[h[(j - i) % n] for j in range(n)] for i in range(n)]
            for i in range(n):
                for j in range(n):
                    g = sum(H[i][k] * H[j][k] for k in range(n))
                    if g != (n if i == j else 0):
                        fail("even Barker n=%d %s: (H H^T)[%d][%d] = %d" % (n, fmt(h), i, j, g))
    print("3. even Barker sequences of length > 2: %d checked (4 | n, periodic off-peak 0, H H^T = nI)"
          % neven)
    if neven == 0:
        fail("no even Barker sequence of length > 2 was checked")

    # 4 ------------------------------------------------------------------------------
    f13 = parse(FORGED13)
    c1 = aperiodic(f13, 1)
    print("4a. forged %s: C(1) = %d, Barker by the plain test: %s"
          % (FORGED13, c1, is_barker_plain(f13)))
    if c1 != 2 or is_barker_plain(f13):
        fail("forged control %s not rejected as expected" % FORGED13)
    if f13 in found.get(13, []):
        fail("forged control %s appears among the sequences found" % FORGED13)
    w13 = list(WITNESSES[13])
    w13[0] = -w13[0]
    bad13 = structure_failures(tuple(w13))
    print("4b. the length-13 witness with h[0] flipped (%s): Barker %s; structure checks failing: %s"
          % (fmt(w13), is_barker_plain(tuple(w13)), sorted(bad13)))
    if not bad13:
        fail("the structure checks pass on the flipped length-13 witness")
    tally = {"aperiodic_eq": 0, "skew": 0, "fold": 0, "doubling": 0, "run_bounds": 0}
    nflip = nflip_barker = 0
    for n in sorted(found):
        if n % 2 == 0:
            continue
        m = (n - 1) // 2
        for h in found[n]:
            for i in range(n):
                g = list(h)
                g[i] = -g[i]
                g = tuple(g)
                nflip += 1
                bad = structure_failures(g)
                for b in bad:
                    tally[b] += 1
                if is_barker_plain(g):
                    nflip_barker += 1
                    if bad:
                        fail("flip %s is Barker but structure checks fail: %s" % (fmt(g), sorted(bad)))
                else:
                    if not bad:
                        fail("flip %s is not Barker but every structure check passes" % fmt(g))
                if i != m and "skew" not in bad:
                    fail("flip %s at %d (not the middle) passes skew" % (fmt(g), i))
    planted = parse("++-+-+-+-+-+-")
    bad_planted = structure_failures(planted)
    if "run_bounds" in bad_planted:
        tally["run_bounds"] += 1
    print("4c. %d single-sign flips of odd Barker sequences (%d of them Barker again); failures per check: %s"
          % (nflip, nflip_barker, tally))
    print("    planted %s (p = 2): failing %s" % (fmt(planted), sorted(bad_planted)))
    for name, c in tally.items():
        if c == 0:
            fail("the check %s never failed on a forged input" % name)

    # 5 ------------------------------------------------------------------------------
    t = time.monotonic()
    deadline = t + ABS_CAP_S
    abs_nodes = [0]
    admitting = []
    try:
        for n in range(1, ABS_MAX + 1, 2):
            sf = sorted(skew_fold_exists(n, deadline, abs_nodes))
            if sf:
                admitting.append(n)
                same = sf == found.get(n, [])
                print("   n=%2d: %d sequences satisfy skew + fold; the same set as the Barker sequences: %s"
                      % (n, len(sf), same))
                if not same:
                    fail("n=%d: the skew + fold sequences differ from the Barker sequences" % n)
        print("5. odd n <= %d admitting skew + fold (no Barker hypothesis): %s (%d nodes, %.1f s)"
              % (ABS_MAX, admitting, abs_nodes[0], time.monotonic() - t))
        if admitting != ODD_LENGTHS:
            fail("abstraction check: %s, expected %s" % (admitting, ODD_LENGTHS))
    except Timeout:
        print("5. UNKNOWN: the abstraction DFS hit its %.0f s cap at n = %d (admitting so far: %s)"
              % (ABS_CAP_S, n, admitting))
        fail("abstraction check UNKNOWN (timeout)")

    print("total %.1f s" % (time.monotonic() - t_all))
    if failures:
        print("%d failure(s)" % len(failures))
        print("VERDICT: FAIL")
        return 1
    print("VERDICT: PASS")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Killed:
        print("KILL file %s present: stopped" % KILL_FILE)
        print("VERDICT: FAIL")
        sys.exit(3)
