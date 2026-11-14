# Suggestions & Ideas for Aligning `temporal` (`rasterops.als`) with the Z Specification

**Repository**: `/home/antigravity/Ruko97/rasterops` (target branch: `origin/temporal` at `b8f845c`; baseline: `main` at `78d8a44`)  
**Reference Specification**: `Z - A case study approach 1.pdf` (Part V, Chapters 10–11, pp. 169–180)  
**Important Note**: Per your request, **no repository files were modified and nothing was pushed**. Also note that OpenJDK 17 is installed in this environment, but **no Alloy Analyzer / Alloy 6 CLI or JAR is installed**, so all Alloy 6 code sketches below are derived from static inspection and should be syntax/model-checked in Alloy 6.

---

## Executive Diagnosis: Why `origin/temporal` Diverges from the Z PDF

1. **Broken `CopySwap ⇔ XorSwap` assertion**: `origin/temporal` checks `(xorswap ; copyswap) implies after^4 (SepPair.map1 = m1 and SepPair.map2 = m2)`. That only checks `CopySwap ∘ XorSwap = Id` (i.e., `copyswap` undoes `xorswap`), **not** `CopySwap ⇔ XorSwap`. Any involution would pass.
2. **Broken `XorSwap ⇔ (Xor₂ ⨟ Xor₁ ⨟ Xor₂)` assertion**: `origin/temporal` checks that `xorswap` and `xorswap2` both imply `m_copy` at `t=3`, without checking equal pre-state domain/enabledness or non-vacuity.
3. **Conflation of Z §11.2 and §11.3**: In the Z PDF, §11.3 (`SepPair`, `CopySwap`, `Xor₁`, `Xor₂`, `XorSwap`) operates directly on `(map₁, map₂)` via `copy` and `xor`. `origin/temporal` forces §11.3 through §11.2's `rasterOp2` on a synthetic `s0 = m1 + m2`, which is actually a *refinement* of §11.3 onto `Display`, not §11.3 itself.
4. **Type error (`offsetBetween` → `rasterOp2`)**: `offsetBetween[m1, m2]` returns `set Pixel`, but `rasterOp2` expects scalar `from: Pixel` (`one Pixel`).
5. **Missing `dom` & arity mismatch**: `dom[...]` is called everywhere without `open util/relation`, and `util/relation/dom` only accepts arity-2 relations, whereas `PixMap` is arity-3 (`Pixel -> ZRange -> lone BitVal`).
6. **`PixMap` partiality over `ZRange`**: `Pixel -> ZRange -> lone BitVal` allows a pixel in `dom[m]` to have values for only *some* `z in ZRange`, violating Z's `Value == Zrange → BitVal` totality.
7. **`one p0` vs `some p0` in `sameshape` / `samepos`**: Z uses `∃ pix₀ : Pixel` (`some p0`). Using `one p0` breaks empty (`none`), full-screen, and periodic/symmetric `PixMap`s (`m_not`, `m_clear`, `m_set` return `none`).
8. **Tiny `2 Pixel` scope & zero `run` witnesses**: `2 Pixel` restricts `Grid` to `1x2` or `2x1` with 1-pixel maps only, and without `run` witnesses, `implies` assertions can pass vacuously.
9. **Other Z-alignment gaps**: `m_set`/`m_clear` are swapped vs literal Z (an intentional fix for a Z textbook erratum that needs a comment); `SameposImpliesSameshape` is higher-order (`all m1, m2: PixMap`) and tautological; `Display` lacks `one` and is unused alongside `deltaDisplay`, `rasterOp1`, `PixelPair`, `p_add`, `p_sub`, `pmin`, `pmax`, `rectangle`; `v_NOT`, `v_AND`, `v_OR`, `v_XOR` are missing; `open util/ternary` is unused.

---

## Part I: 6 Architectural Ideas for Modeling §11.3 (`XorSwap`, `CopySwap`, `⨟`, `⇔`) in Alloy 6

Why naive `xorswap iff copyswap` (on `main`) fails in Alloy 6:
- **Step-count mismatch**: `xor1 ; xor2 ; xor1` spans **3 transitions** (`t=0 → 1 → 2 → 3`), whereas `copyswap` spans **1 transition** (`t=0 → 1`).
- **Intermediate-state mismatch**: `xorswap` (`xor1 ; xor2 ; xor1`) and `xorswap2` (`xor2 ; xor1 ; xor2`) differ at `t=1` and `t=2`, even though they reach the same `t=3` state. In Z, `⨟` hides intermediate states; in Alloy 6, `;` exposes them.

Here are **6 concrete ways** to model this faithfully in Alloy 6:

### Idea 1: Post-State / End-to-End Effect Equivalence (`after^3` vs `after`)
Keep `one sig SepPair` and assert that `xorswap` (at `t=3`), `xorswap2` (at `t=3`), and `copyswap` (at `t=1`) all reach the same swapped state from `(m1, m2)`.

```alloy
pred copyswap {
    deltaseppair
    SepPair.map1' = m_copy[SepPair.map2, SepPair.map1]
    SepPair.map2' = m_copy[SepPair.map1, SepPair.map2]
}
pred xor1 {
    deltaseppair
    SepPair.map1' = m_xor[SepPair.map2, SepPair.map1]
    SepPair.map2' = SepPair.map2
}
pred xor2 {
    deltaseppair
    SepPair.map1' = SepPair.map1
    SepPair.map2' = m_xor[SepPair.map1, SepPair.map2]
}
pred xorswap  { xor1 ; xor2 ; xor1 }
pred xorswap2 { xor2 ; xor1 ; xor2 }

pred swappedFrom[m1, m2: PixMap] {
    SepPair.map1 = m_copy[m2, m1]
    SepPair.map2 = m_copy[m1, m2]
}

assert XorSwapSymmetry {
    let m1 = SepPair.map1, m2 = SepPair.map2 |
        (xorswap  implies after after after swappedFrom[m1, m2]) and
        (xorswap2 implies after after after swappedFrom[m1, m2])
}

assert CopySwapMatchesXorSwap {
    let m1 = SepPair.map1, m2 = SepPair.map2 |
        (copyswap implies after swappedFrom[m1, m2]) and
        (xorswap  implies after after after swappedFrom[m1, m2])
}
```
- **Pros**: Minimal diff from `origin/temporal`; fixes the `xorswap ; copyswap` bug immediately.
- **Cons**: Uses `m_copy` in `swappedFrom` as the oracle; must be paired with `run` witnesses to rule out vacuity.

### Idea 2: Stuttering Alignment (`copyswap ; stutter ; stutter`) + `eventually`
Add a `stutter` step so `copyswap3` takes 3 transitions just like `xorswap`, or use `eventually` for liveness.

```alloy
pred stutter {
    SepPair.map1' = SepPair.map1
    SepPair.map2' = SepPair.map2
}
pred copyswap3 { copyswap ; stutter ; stutter }
```
- **Pros**: Uniform 3-step horizon (`4 steps`); mirrors Z's prose note that `CopySwap` cannot literally happen in one simultaneous hardware step.
- **Cons**: Still cannot write `xorswap iff copyswap3` (they differ at `t=1, 2`). `eventually` alone is weaker than `after after after` because a lasso trace could satisfy `eventually` at a different step.

### Idea 3: Immutable `one sig Pre` Snapshot
Capture Z's unprimed `SepPair` in a rigid (non-`var`) `one sig Pre { map1, map2: PixMap } { seppair[map1, map2] }`, and check `(startsAtPre and xorswap) implies after after after (...)`.
- **Pros**: Eliminates any confusion about which `after` depth `let m1 = SepPair.map1` binds to; reads like Z's unprimed `SepPair` vs primed `SepPair'`.
- **Cons**: Requires `startsAtPre` in assertions/runs (never in a global `fact`).

### Idea 4: Dual-System Side-by-Side Trace Comparison (`XorSys` vs `CopySys`) — *Oracle-Free!*
Make `SepPair` non-`one` with instances `XorSys`, `XorSys2`, `CopySys` starting from the same initial state, and assert their `t=3` states are **equal** (without hardcoding `m_copy` in the assertion!):

```alloy
abstract sig SepPair { var map1, map2: PixMap }
one sig XorSys, XorSys2, CopySys extends SepPair {}

pred sameInit[a, b: SepPair] { a.map1 = b.map1 and a.map2 = b.map2 }

assert CopySwapIffXorSwap_Dual {
    (sameInit[XorSys, CopySys] and sameInit[XorSys, XorSys2] and
     xorswap[XorSys] and xorswap2[XorSys2] and
     (copyswap[CopySys] ; stutter[CopySys] ; stutter[CopySys]))
    implies after after after (
        XorSys.map1 = CopySys.map1 and XorSys.map2 = CopySys.map2 and
        XorSys.map1 = XorSys2.map1 and XorSys.map2 = XorSys2.map2
    )
}
check CopySwapIffXorSwap_Dual for 4 but exactly 1 Grid, 4 Pixel, 4 steps
```
- **Pros**: Proves observational equivalence between `CopySwap`, `XorSwap`, and `XorSwap2` without circularly using `m_copy` as the oracle; parameterizing `xor1[s: SepPair]` is clean Alloy 6.
- **Cons**: Slightly larger SAT problem (3 `SepPair` instances in parallel).

### Idea 5: Hybrid Z Schema-Calculus Bridge (`SepPairState` + Temporal Wrapper) — *Exact `iff`!*
Model Z's `SepPair` as an immutable state atom `sig SepPairState`, express Z's `⨟` literally via existential intermediate states `some s1, s2: SepPairState`, prove Z's **literal** `iff` theorems, AND wrap it in a temporal `one sig SepPair { var state: SepPairState }` for Alloy 6 trace visualization:

```alloy
sig SepPairState { map1, map2: PixMap } {
    mappair[map1, map2]
    not overlaps[map1, map2]
}
pred z_copyswap[s, s': SepPairState] { ... }
pred z_xor1[s, s': SepPairState] { ... }
pred z_xor2[s, s': SepPairState] { ... }

pred z_xorswap[s, s': SepPairState] {
    some s1, s2: SepPairState | z_xor1[s, s1] and z_xor2[s1, s2] and z_xor1[s2, s']
}
pred z_xorswap2[s, s': SepPairState] {
    some s1, s2: SepPairState | z_xor2[s, s1] and z_xor1[s1, s2] and z_xor2[s2, s']
}

assert Z_XorSwapSymmetry    { all s, s': SepPairState | z_xorswap[s, s'] iff z_xorswap2[s, s'] }
assert Z_CopySwapIffXorSwap { all s, s': SepPairState | z_copyswap[s, s'] iff z_xorswap[s, s'] }
check Z_XorSwapSymmetry    for 4 but exactly 1 Grid, 4 Pixel, 4 SepPairState
check Z_CopySwapIffXorSwap for 4 but exactly 1 Grid, 4 Pixel, 4 SepPairState

-- Thin Alloy 6 temporal wrapper for traces:
one sig SepPair { var state: SepPairState }
pred xor1     { z_xor1[SepPair.state, SepPair.state'] }
pred xor2     { z_xor2[SepPair.state, SepPair.state'] }
pred copyswap { z_copyswap[SepPair.state, SepPair.state'] }
pred xorswap  { xor1 ; xor2 ; xor1 }
```
- **Pros**: **10/10 Z fidelity** — `z_copyswap[s, s'] iff z_xorswap[s, s']` is literally `ΔSepPair ⊢ CopySwap ⇔ XorSwap`.
- **Cons / Trap**: Scope of `SepPairState` **must be `>= 4`** (for `s, s1, s2, s'`), otherwise `z_xorswap` could miss valid intermediate states!

### Idea 6: Separate §11.3 Direct (`m_copy`/`m_xor`) from §11.2 (`Display` + `RasterOp2`) via a Refinement Theorem
Instead of replacing `m_copy`/`m_xor` in §11.3 with `rasterOp2` (as `origin/temporal` did), keep §11.3 pure per the Z PDF, and add an explicit **Refinement Theorem** showing that `RasterOp2` on `Display.screen` implements `Xor1` (and `CopySwap`) on embedded disjoint `SepPair` regions without disturbing the rest of the screen:

```alloy
assert RasterOp2RefinesXor1 {
    all p0: Pixel |
        let s = Display.screen, m1 = SepPair.map1, m2 = SepPair.map2 |
            (seppair[m1, m2] and (m1 + m2) in s and (dom[m1]).(shift[p0]) = dom[m2] and
             RasterOp2[dom[m1], p0, XOR])
            implies (
                dom[m1] <: Display.screen' = m_xor[m2, m1] and
                dom[m2] <: Display.screen' = m2 and
                (dom[s] - dom[m1]) <: Display.screen' = (dom[s] - dom[m1]) <: s
            )
}
```
- **Pros**: Fixes `offsetBetween` cleanly (quantifies `p0: Pixel`), connects §11.2 (`Display`) and §11.3 (`SepPair`) meaningfully, and checks frame preservation on `dom[s] - dom[m1]`.

---

## Part II: Foundational & Semantic Fixes (Chapters 10–11)

### Idea 7: Fix `dom` Arity & `PixMap` Totality Over `ZRange`
- **Option 7a (Binary `PixMap` via `sig Value` — Most Z-Faithful)**:
  Promote `Value` to `sig Value { bits: Int -> BitVal } { bits in ZRange -> one BitVal }` with `fact CanonicalValues { all v1, v2: Value | v1.bits = v2.bits implies v1 = v2 }`, and `let PixMap = Pixel -> lone Value`. Then `open util/relation` works natively on `dom[m]`, `ZRange` totality is automatic, and `Value` ops become first-order! *(Trade-off: needs `Value` scope `>= 2^zsize`.)*
- **Option 7b (Minimal diff — Keep ternary `PixMap`)**:
  Remove unused `open util/ternary`, define `fun dom[m: PixMap]: set Pixel { m.BitVal.ZRange }`, and enforce `pred validPixMap[m: PixMap] { all p: dom[m], z: ZRange | one m[p][z] }` in `TestMaps`, `seppair`, and `DeltaDisplay`.

### Idea 8: Fix `sameshape` / `samepos` (`one p0` → `some p0`) & `offsetBetween`
- Change `one p0: Pixel` to `some p0: Pixel` in `sameshape` and `samepos` to match Z's `∃ pix₀ : Pixel`.
- Note why `one p0` was originally written: for periodic/full-screen `PixMap`s, multiple `p0` satisfy `(dom[m1]).(shift[p0]) = dom[m2]`, which would make `samepos` non-functional in `m_nand`.
- **Clean fix**: Keep `some p0` in `sameshape` (faithful to Z), and if keeping `offsetBetween` in §11.3, quantify `some p12: offsetBetween[m1, m2] | ... rasterOp2[..., p12, ...]` instead of passing `set Pixel` to `from: Pixel`.

### Idea 9: Fix `Display`, `DeltaDisplay`, `RasterOp1`, `RasterOp2` (§11.2)
- Change `sig Display` to `one sig Display { var screen: PixMap }`.
- Convert `RasterOp1` and `RasterOp2` into temporal predicates on `DeltaDisplay` (enforcing `dom[Display.screen'] = dom[Display.screen]` and `mappair` guard on `RasterOp2`), rather than leaving them as unused pure functions.

### Idea 10: Document `m_set` vs `m_clear` Z-Textbook Erratum & Add Missing `Value` Ops
- Keep `m_set[m] = m_nand[m, m_not[m]]` and `m_clear[m] = m_not[m_set[m]]` (they are mathematically right for `ClearVal=0, SetVal=1`, whereas literal Z `clear map = map nand (not map)` yields `SetVal=1` and would break `m_copy`), and add an explicit comment explaining this intentional Z erratum fix.
- Add the missing §11.1.1 `Value` operations: `v_NOT`, `v_AND`, `v_OR`, `v_XOR`.
- Add Z's explicit domain guards to `p_add` (`p1.x < minus[Grid.xsize, p2.x] and ...`) and `p_sub` (`p_leq[p2, p1]`).

### Idea 11: Fix `SameposImpliesSameshape` Higher-Order Quantification
Rewrite `all m1, m2: PixMap` using `all t1, t2: TestMaps` (matching `MapPairImpliesNANDCommutative`) so Alloy's solver can actually check it without higher-order skolemization failure.

---

## Part III: Verification, Scopes, Missing Z Laws, & Hygiene

### Idea 12: Add Non-Vacuity `run` Witnesses & Widen `2 Pixel` → `4 Pixel` / `6 Pixel`
- Replace `2 Pixel` (which only tests 1-pixel `PixMap`s in `1x2`/`2x1` grids) with `4 Pixel` (allows `2x2` grids with 2-pixel maps) or `6 Pixel` (`2x3`/`3x2` grids).
- Add explicit `run` predicates requiring `#dom[SepPair.map1] >= 2` and `SepPair.map1 != m_copy[SepPair.map2, SepPair.map1]` for `xorswap`, `xorswap2`, `copyswap`, and `RasterOp2`.

### Idea 13: Check Missing Z Laws from Chapters 10–11
Add `assert` + `check` for:
- `ShiftIsBijection`: `all p0: Pixel | (Pixel -> one Pixel) and (one Pixel -> Pixel)` for `shift[p0]`
- `RectOrderLaw` (§10.2.1): if `rect` is defined via `(x1..x2) × (y1..y2)`, verify equivalence to `{ p: Pixel | p_leq[p1, p] and p_leq[p, p2] }`
- `XorInvolution` (§11.1.2): `mappair[m1, m2] implies m_xor[m1, m_xor[m1, m2]] = m2`
- `CopyCorrectness` (§11.1.2): `m_copy[m1, m2]` preserves `dom[m2]` and copies `m1`'s values
- Optionally `setval` + `SetvalIdempotence` and `⊕/` (distributed override) if full §10.2.2 coverage is desired.

### Idea 14: 1-to-1 Z Section Headers, Naming Alignment, & Dead-Code Cleanup
- Add `-- Section 10.2.1` .. `-- Section 11.3` headers mirroring the PDF.
- Align names to Z (`DeltaDisplay`, `DeltaSepPair`, `CopySwap`, `Xor1`, `Xor2`, `XorSwap`, `Xsize`/`Ysize`/`Zsize`).
- Remove unused `open util/ternary`, duplicate `some maps` in `TestMaps`, unused `BitVal.bit` (or use it), tautological `AtMostOneBitVal`, and unify `--` comments and indentation.

---

## Part IV: 3 Recommended Recipes

| Recipe | Ideas Combined | Best For |
|---|---|---|
| **A. Minimal Surgical Fix** | Idea 1 (`after^3`) + Idea 7b (`dom` + `validPixMap`) + Idea 8 (`some p0` + `some p12: offsetBetween`) + Idea 12 (`run` + `4 Pixel`) | Smallest diff on `origin/temporal` that fixes all type/semantic bugs |
| **B. Cleanest Temporal-First** | Idea 4 (Dual-System `XorSys` vs `CopySys`) + Idea 6 (§11.2 Refinement) + Idea 7b + Idea 8 + Idea 12 + Idea 14 | Oracle-free temporal equivalence + clean separation of §11.2 and §11.3 |
| **C. Maximum Z-Fidelity Hybrid** | Idea 5 (`SepPairState` + `⨟` + temporal wrapper) + Idea 6 (§11.2 Refinement) + Idea 7a (`sig Value` binary `PixMap`) + Idea 10 + Idea 12 + Idea 13 + Idea 14 | Closest possible 1-to-1 match to the Z PDF with literal `⇔` theorems AND Alloy 6 traces |
