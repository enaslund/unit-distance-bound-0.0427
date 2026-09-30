module

public import UnitDistance.Sqrt241.Numerics.PairMassTables
public import UnitDistance.Sqrt241.Numerics.RatLog

@[expose] public section
set_option backward.privateInPublic true


/-!
# Rational arithmetic of the pair-mass certificate

Every quantity here is a rational number computed by structural recursion, so
the finite inequalities of the certificate are decided by kernel evaluation.
The analytic meaning is proved in `PairMassCell.lean`:

* `cellLo`, `cellHi`: the polynomial at the lower-left and upper-right corner of
  the cell `[i/N,(i+1)/N] × [j/N,(j+1)/N]` (its minimum and maximum there);
* `cellRho h lo hi`: a bound for `|P/h − 1|` on the cell;
* `binA h m`, `tailQ ρ`: the degree-three binomial polynomial
  `∑_{k≤3} C(p,k)(P/h−1)^k` rewritten in powers of `P`, and its uniform tail;
* `cellCoeff`: the monomial coefficients of that majorant (through `cPow`);
* `muLo`, `muHi`: directed enclosures of the beta moments
  `q ((r^(q+m) − l^(q+m))/(q+m))` from enclosures `XL`, `XU` of `(k/N)^q`;
* `cellEbar`: the directed upper evaluation of the exact cell integral of the
  majorant, and `massTotal` the sum over all cells weighted by `HTab ≥ h^p`.
-/

namespace UnitDistance.Sqrt241.Witness.MassCert

/-- `∑_{i<n} f i`, by structural recursion. -/
def sumRange (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => sumRange f n + f n

theorem sumRange_cast (f : ℕ → ℚ) (n : ℕ) :
    ((sumRange f n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, ((f i : ℚ) : ℝ) := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih =>
    rw [sumRange, Finset.sum_range_succ, ← ih]
    push_cast
    ring

/-- The mass exponent `p = 2/(1+δ)`. -/
def pQ : ℚ := 20000 / 10427

/-- The beta exponent `q = s·p − 1`. -/
def qQ : ℚ := 12493117 / 10427000

/-- Generalized binomial coefficients `C(x, k)`. -/
def gchoose (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => gchoose x n * (x - n) / (n + 1)

/-- The pair polynomial at rational arguments. -/
def PQ (x y : ℚ) : ℚ :=
  sumRange (fun i => sumRange (fun j => cPow 1 i j * x ^ i * y ^ j) 4) 4

def cellLo (N i j : ℕ) : ℚ := PQ ((i : ℚ) / N) ((j : ℚ) / N)

def cellHi (N i j : ℕ) : ℚ := PQ (((i : ℚ) + 1) / N) (((j : ℚ) + 1) / N)

def cellRho (h lo hi : ℚ) : ℚ := max (hi / h - 1) (1 - lo / h)

/-- Coefficients of `∑_{k≤3} C(p,k) (P/h − 1)^k = ∑_{m≤3} binA h m · P^m`. -/
def binA (h : ℚ) : ℕ → ℚ
  | 0 => gchoose pQ 0 - gchoose pQ 1 + gchoose pQ 2 - gchoose pQ 3
  | 1 => (gchoose pQ 1 - 2 * gchoose pQ 2 + 3 * gchoose pQ 3) / h
  | 2 => (gchoose pQ 2 - 3 * gchoose pQ 3) / h ^ 2
  | _ => gchoose pQ 3 / h ^ 3

/-- Uniform bound for the binomial tail after degree three. -/
def tailQ (ρ : ℚ) : ℚ := |gchoose pQ 4| * ρ ^ 4 / (1 - ρ)

/-- Monomial coefficients of the cell majorant. -/
def cellCoeff (h ρ : ℚ) (i j : ℕ) : ℚ :=
  sumRange (fun m => binA h m * cPow m i j) 4 + (if i = 0 ∧ j = 0 then tailQ ρ else 0)

/-- Lower enclosure of the beta moment of `t^m` on `[k/N, (k+1)/N]`. -/
def muLo (N : ℕ) (XL XU : ℕ → ℚ) (k m : ℕ) : ℚ :=
  max 0 (qQ / (qQ + m) * ((((k : ℚ) + 1) / N) ^ m * XL (k + 1) - ((k : ℚ) / N) ^ m * XU k))

/-- Upper enclosure of the beta moment of `t^m` on `[k/N, (k+1)/N]`. -/
def muHi (N : ℕ) (XL XU : ℕ → ℚ) (k m : ℕ) : ℚ :=
  qQ / (qQ + m) * ((((k : ℚ) + 1) / N) ^ m * XU (k + 1) - ((k : ℚ) / N) ^ m * XL k)

/-- Directed upper bound of `d x y` for `x ∈ [x0, x1]`, `y ∈ [y0, y1]`, `x0, y0 ≥ 0`. -/
def dirU (d x0 x1 y0 y1 : ℚ) : ℚ := if 0 ≤ d then d * x1 * y1 else d * x0 * y0

/-- Directed upper evaluation of the exact cell integral of the majorant. -/
def cellEbar (N : ℕ) (XL XU : ℕ → ℚ) (i j : ℕ) (h : ℚ) : ℚ :=
  sumRange (fun a => sumRange (fun b =>
    dirU (cellCoeff h (cellRho h (cellLo N i j) (cellHi N i j)) a b)
      (muLo N XL XU i a) (muHi N XL XU i a) (muLo N XL XU j b) (muHi N XL XU j b)) 10) 10

/-- The certified total over all cells. -/
def massTotal (N : ℕ) (XL XU : ℕ → ℚ) (hTab HTab : ℕ → ℕ → ℚ) : ℚ :=
  sumRange (fun i => sumRange (fun j =>
    HTab i j * max (cellEbar N XL XU i j (hTab i j)) 0) N) N

/-! ## Assembling the certificate from separately checked cases

The certificate of `PairMassData.lean` checks every grid point and every cell by
its own lemma, so that each kernel reduction stays small. The lemmas below
combine those cases. -/

theorem sumRange_le_sumRange {f g : ℕ → ℚ} {n : ℕ} (h : ∀ i, i < n → f i ≤ g i) :
    sumRange f n ≤ sumRange g n := by
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    simp only [sumRange]
    exact add_le_add (ih fun i hi => h i (Nat.lt_succ_of_lt hi)) (h n (Nat.lt_succ_self n))

/-- The certified total is at most the sum of any per-cell upper bounds `C i j`
for the cell contributions. -/
theorem massTotal_le_of_cells (N : ℕ) (XL XU : ℕ → ℚ) (hTab HTab C : ℕ → ℕ → ℚ)
    (hC : ∀ i, i < N → ∀ j, j < N → HTab i j * max (cellEbar N XL XU i j (hTab i j)) 0 ≤ C i j) :
    massTotal N XL XU hTab HTab ≤ sumRange (fun i => sumRange (fun j => C i j) N) N :=
  sumRange_le_sumRange fun i hi => sumRange_le_sumRange fun j hj => hC i hi j hj

theorem forall_lt_zero (P : ℕ → Prop) : ∀ i, i < 0 → P i :=
  fun i hi => absurd hi (Nat.not_lt_zero i)

/-- `∀ i < n + 1, P i` from `∀ i < n, P i` and `P n`. -/
theorem forall_lt_succ_of {P : ℕ → Prop} {n : ℕ} (h : ∀ i, i < n → P i) (hn : P n) :
    ∀ i, i < n + 1 → P i := by
  intro i hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · exact h i hi
  · exact hn

end UnitDistance.Sqrt241.Witness.MassCert
