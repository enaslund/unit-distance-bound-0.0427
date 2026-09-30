module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! Collection of actual group words with central commutation corrections.
Every identity is proved from actual multiplication and centrality equations. -/
noncomputable section
namespace UnitDistance.ClassTwo.Collection
abbrev F := ZMod 2
variable {G W ι : Type*} [Group G] [AddCommGroup W] [Module F W]

/-- A binary power of an actual group element. -/
def bit (g : G) (t : F) : G := if t=0 then 1 else g

@[simp] theorem bit_zero (g : G) : bit g 0=1 := by simp [bit]
@[simp] theorem bit_one (g : G) : bit g 1=g := by simp [bit]

theorem binary_cases (t : F) : t=0 ∨ t=1 := by
  have h : ∀ t : F, t=0 ∨ t=1 := by decide +kernel
  exact h t

theorem bit_add (g : G) (hg : g^2=1) (a b : F) :
    bit g (a+b)=bit g a*bit g b := by
  have htwo : (1+1 : F)=0 := by decide
  rcases binary_cases a with rfl | rfl <;>
    rcases binary_cases b with rfl | rfl <;>
    simp [htwo,← pow_two,hg]

variable (z : Multiplicative W →* G)
  (hz : ∀ w g, Commute (z w) g)

/-- A displayed swap equation holds for either binary power. -/
theorem bit_swap (g h : G) (c : W) (hs : g*h=z (Multiplicative.ofAdd c)*h*g) (t : F) :
    bit g t*h=z (Multiplicative.ofAdd (t • c))*h*bit g t := by
  rcases binary_cases t with rfl | rfl
  · simp
  · simpa using hs

/-- The actual ordered word associated to a list of generators and binary exponents. -/
def word (g : ι → G) (l : List ι) (v : ι → F) : G :=
  (l.map fun i => bit (g i) (v i)).prod

@[simp] theorem word_nil (g : ι → G) (v : ι → F) : word g [] v=1 := rfl
@[simp] theorem word_cons (g : ι → G) (i : ι) (l : List ι) (v : ι → F) :
    word g (i::l) v=bit (g i) (v i)*word g l v := rfl
@[simp] theorem word_append (g : ι → G) (l l' : List ι) (v : ι → F) :
    word g (l++l') v=word g l v*word g l' v := by simp [word]

def correction (c : ι → W) (l : List ι) (v : ι → F) : W :=
  (l.map fun i => v i • c i).sum

@[simp] theorem correction_nil (c : ι → W) (v : ι → F) : correction c [] v=0 := rfl
@[simp] theorem correction_cons (c : ι → W) (i : ι) (l : List ι) (v : ι → F) :
    correction c (i::l) v=v i • c i+correction c l v := rfl

include hz in
/-- Moving a generator across an actual ordered word accumulates the
sum of its actual central commutation corrections. -/
theorem word_swap (g : ι → G) (h : G) (c : ι → W) (l : List ι) (v : ι → F)
    (hs : ∀ i ∈ l, g i*h=z (Multiplicative.ofAdd (c i))*h*g i) :
    word g l v*h=z (Multiplicative.ofAdd (correction c l v))*h*word g l v := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have ht := ih (fun j hj => hs j (by simp [hj]))
    have hi := bit_swap z (g i) h (c i) (hs i (by simp)) (v i)
    simp only [word_cons,correction_cons]
    rw [show Multiplicative.ofAdd (v i • c i+correction c l v)=
      Multiplicative.ofAdd (v i • c i)*Multiplicative.ofAdd (correction c l v) from rfl,map_mul]
    calc
      (bit (g i) (v i)*word g l v)*h = bit (g i) (v i)*(word g l v*h) := by group
      _ = bit (g i) (v i)*(z (Multiplicative.ofAdd (correction c l v))*h*word g l v) := by rw [ht]
      _ = z (Multiplicative.ofAdd (correction c l v))*(bit (g i) (v i)*h)*word g l v := by
        rw [← mul_assoc,← mul_assoc,(hz _ _).symm.eq]
        group
      _ = z (Multiplicative.ofAdd (correction c l v))*
          (z (Multiplicative.ofAdd (v i • c i))*h*bit (g i) (v i))*word g l v := by rw [hi]
      _ = _ := by
        simp only [← mul_assoc]
        rw [(hz (Multiplicative.ofAdd (correction c l v))
          (z (Multiplicative.ofAdd (v i • c i)))).eq]

/-- Ordered words depend only on exponents at positions occurring in the list. -/
theorem word_congr (g : ι → G) (l : List ι) {v w : ι → F}
    (h : ∀ i ∈ l, v i=w i) : word g l v=word g l w := by
  unfold word
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [h i hi]

include hz in
/-- Right multiplication toggles the selected exponent, with precisely
the central correction from the generators to its right. -/
theorem word_toggle [DecidableEq ι] (g : ι → G) (i : ι) (left right : List ι)
    (v : ι → F) (c : ι → W) (hi : g i^2=1)
    (hil : i ∉ left) (hir : i ∉ right)
    (hs : ∀ j ∈ right, g j*g i=z (Multiplicative.ofAdd (c j))*g i*g j) :
    word g (left++i::right) v*g i =
      z (Multiplicative.ofAdd (correction c right v))*
        word g (left++i::right) (v+Pi.single i 1) := by
  have hl : word g left (v+Pi.single i 1)=word g left v := by
    apply word_congr
    intro j hj
    have hji : j≠i := by intro he; subst j; exact hil hj
    simp [Pi.single_apply,hji]
  have hr : word g right (v+Pi.single i 1)=word g right v := by
    apply word_congr
    intro j hj
    have hji : j≠i := by intro he; subst j; exact hir hj
    simp [Pi.single_apply,hji]
  simp only [word_append,word_cons,hl,hr,Pi.add_apply,Pi.single_eq_same]
  rw [bit_add (g i) hi,bit_one]
  have ht := word_swap z hz g (g i) c right v hs
  calc
    (word g left v*(bit (g i) (v i)*word g right v))*g i =
        word g left v*bit (g i) (v i)*(word g right v*g i) := by group
    _ = word g left v*bit (g i) (v i)*
        (z (Multiplicative.ofAdd (correction c right v))*g i*word g right v) := by rw [ht]
    _ = _ := by
      simpa only [mul_assoc] using congrArg
        (fun a => a*g i*word g right v)
        (hz (Multiplicative.ofAdd (correction c right v))
          (word g left v*bit (g i) (v i))).symm.eq

/-- The collected central correction is linear in the binary exponents. -/
def correctionMap (c : ι → W) (l : List ι) : (ι → F) →ₗ[F] W where
  toFun := correction c l
  map_add' v w := by
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [correction_cons,Pi.add_apply,add_smul,ih]
      abel
  map_smul' r v := by
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [correction_cons,Pi.smul_apply,smul_eq_mul,mul_smul,ih,
        RingHom.id_apply,smul_add]

end UnitDistance.ClassTwo.Collection
