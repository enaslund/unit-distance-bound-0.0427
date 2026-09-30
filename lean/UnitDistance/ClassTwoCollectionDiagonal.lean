module

public import UnitDistance.ClassTwoCollection

@[expose] public section
set_option backward.privateInPublic true


/-! Collection with central generator squares, for the actual local
quadratic quotient whose generators need not be involutions. -/
noncomputable section
namespace UnitDistance.ClassTwo.Collection
variable {G W ι : Type*} [Group G] [AddCommGroup W] [Module F W]
  (z : Multiplicative W →* G) (hz : ∀ w g,Commute (z w) g)

/-- Toggling a bit contributes the actual generator square. -/
theorem bit_right_diagonal (g : G) (d : W) (hg : g^2=z (Multiplicative.ofAdd d)) (t : F) :
    bit g t*g=z (Multiplicative.ofAdd (t • d))*bit g (t+1) := by
  rcases binary_cases t with rfl | rfl
  · simp
  · have htwo : (1+1 : F)=0 := by decide
    simpa only [bit_one,one_smul,htwo,bit_zero,mul_one,pow_two] using hg

include hz in
/-- The ordered-word collection formula with its true central diagonal. -/
theorem word_toggle_diagonal [DecidableEq ι] (g : ι → G) (i : ι) (left right : List ι)
    (v : ι → F) (c : ι → W) (d : W) (hi : g i^2=z (Multiplicative.ofAdd d))
    (hil : i∉left) (hir : i∉right)
    (hs : ∀ j∈right,g j*g i=z (Multiplicative.ofAdd (c j))*g i*g j) :
    word g (left++i::right) v*g i =
      z (Multiplicative.ofAdd (correction c right v+v i • d))*
        word g (left++i::right) (v+Pi.single i 1) := by
  have hl : word g left (v+Pi.single i 1)=word g left v := by
    apply word_congr
    intro j hj
    have hji : j≠i := by intro h; subst j; exact hil hj
    simp [Pi.single_apply,hji]
  have hr : word g right (v+Pi.single i 1)=word g right v := by
    apply word_congr
    intro j hj
    have hji : j≠i := by intro h; subst j; exact hir hj
    simp [Pi.single_apply,hji]
  simp only [word_append,word_cons,hl,hr,Pi.add_apply,Pi.single_eq_same]
  have ht := word_swap z hz g (g i) c right v hs
  rw [show Multiplicative.ofAdd (correction c right v+v i • d)=
    Multiplicative.ofAdd (correction c right v)*Multiplicative.ofAdd (v i • d) from rfl,map_mul]
  calc
    (word g left v*(bit (g i) (v i)*word g right v))*g i =
        (word g left v*bit (g i) (v i))*(word g right v*g i) := by group
    _ = (word g left v*bit (g i) (v i))*(z (Multiplicative.ofAdd (correction c right v))*g i*word g right v) := by rw [ht]
    _ = z (Multiplicative.ofAdd (correction c right v))*word g left v*
        (bit (g i) (v i)*g i)*word g right v := by
      rw [← mul_assoc,← mul_assoc,(hz _ _).symm.eq]
      group
    _ = z (Multiplicative.ofAdd (correction c right v))*word g left v*
        (z (Multiplicative.ofAdd (v i • d))*bit (g i) (v i+1))*word g right v := by
      rw [bit_right_diagonal z (g i) d hi]
    _ = _ := by
      simpa only [mul_assoc] using congrArg
        (fun q => z (Multiplicative.ofAdd (correction c right v))*q*
          bit (g i) (v i+1)*word g right v)
        (hz (Multiplicative.ofAdd (v i • d)) (word g left v)).symm.eq

end UnitDistance.ClassTwo.Collection
