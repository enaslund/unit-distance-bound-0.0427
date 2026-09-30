module

public import UnitDistance.FiniteCertificates.LogEnclosureCompactRun20260920

@[expose] public section
set_option backward.privateInPublic true


namespace UnitDistance.Witness.FiniteCertificates

theorem power_bound_5_0 :
    (shellWeights ⟨5, by decide⟩ ⟨0, by decide⟩ : ℝ)^p ≤ powerUpper ⟨5, by decide⟩ ⟨0, by decide⟩ := by
  norm_num [shellWeights, powerUpper, Matrix.cons_val]

theorem weight_log_5_1 :
    (-10832194169745255319 : ℝ) / 1000000000000000000 ≤ Real.log ((19753217475271 : ℝ) / 1000000000000000000) ∧
    Real.log ((19753217475271 : ℝ) / 1000000000000000000) ≤ (-10832194169745255317 : ℝ) / 1000000000000000000 := by
  have hb : (25816071921386963257 : ℝ) / 100000000000000000000 ≤ Real.log ((19753217475271 : ℝ) / 15258789062500) ∧
      Real.log ((19753217475271 : ℝ) / 15258789062500) ≤ (12908035960693481629 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((19753217475271 : ℚ) / 15258789062500) 25
      ((25816071921386963257 : ℚ) / 100000000000000000000)
      ((12908035960693481629 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (19753217475271 : ℝ) / 15258789062500) (l := (19753217475271 : ℝ) / 15258789062500)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((19753217475271 : ℝ) / 1000000000000000000) ((19753217475271 : ℝ) / 15258789062500) (-16) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_5_1 :
    (-2079468195859510411 : ℝ) / 100000000000000000 ≤ Real.log ((4655371856514197 : ℝ) / 5000000000000000000000000) ∧
    Real.log ((4655371856514197 : ℝ) / 5000000000000000000000000) ≤ (-5198670489648776027 : ℝ) / 250000000000000000 := by
  have hb : (4330503992270003017 : ℝ) / 6250000000000000000 ≤ Real.log ((1999466987444728067 : ℝ) / 1000000000000000000) ∧
      Real.log ((1999466987444728067 : ℝ) / 1000000000000000000) ≤ (69288063876320048273 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1999466987444728067 : ℚ) / 1000000000000000000) 25
      ((4330503992270003017 : ℚ) / 6250000000000000000)
      ((69288063876320048273 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (595887597633817216 : ℝ) / 298023223876953125) (l := (1999466987444728067 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((4655371856514197 : ℝ) / 5000000000000000000000000) ((595887597633817216 : ℝ) / 298023223876953125) (-31) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_5_1 :
    (shellWeights ⟨5, by decide⟩ ⟨1, by decide⟩ : ℝ)^p ≤ powerUpper ⟨5, by decide⟩ ⟨1, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (19753217475271 : ℝ) / 1000000000000000000)
    (by norm_num : 0 < (4655371856514197 : ℝ) / 5000000000000000000000000) witness_basic.2.2.1.le
    weight_log_5_1.2 power_upper_log_5_1.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_5_2 :
    (-11881728025149082053 : ℝ) / 500000000000000000 ≤ Real.log ((23912895762421 : ℝ) / 500000000000000000000000) ∧
    Real.log ((23912895762421 : ℝ) / 500000000000000000000000) ≤ (-2970432006287270513 : ℝ) / 125000000000000000 := by
  have hb : (24834763464996086223 : ℝ) / 50000000000000000000 ≤ Real.log ((410820421009020723 : ℝ) / 250000000000000000) ∧
      Real.log ((410820421009020723 : ℝ) / 250000000000000000) ≤ (49669526929992172447 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((410820421009020723 : ℚ) / 250000000000000000) 25
      ((24834763464996086223 : ℚ) / 50000000000000000000)
      ((49669526929992172447 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (97947221042876416 : ℝ) / 59604644775390625) (l := (410820421009020723 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((23912895762421 : ℝ) / 500000000000000000000000) ((97947221042876416 : ℝ) / 59604644775390625) (-35) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_5_2 :
    (-9123793444973399807 : ℝ) / 200000000000000000 ≤ Real.log ((15414671150223429 : ℝ) / 1000000000000000000000000000000000000) ∧
    Real.log ((15414671150223429 : ℝ) / 1000000000000000000000000000000000000) ≤ (-45618967224866999033 : ℝ) / 1000000000000000000 := by
  have hb : (12874669208939138709 : ℝ) / 100000000000000000000 ≤ Real.log ((227480394950852509 : ℝ) / 200000000000000000) ∧
      Real.log ((227480394950852509 : ℝ) / 200000000000000000) ≤ (1287466920893913871 : ℝ) / 10000000000000000000 := by
    have h := log_enclosure_of_rat
      ((227480394950852509 : ℚ) / 200000000000000000) 25
      ((12874669208939138709 : ℚ) / 100000000000000000000)
      ((1287466920893913871 : ℚ) / 10000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (16551377117201082661994496 : ℝ) / 14551915228366851806640625) (l := (227480394950852509 : ℝ) / 200000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((15414671150223429 : ℝ) / 1000000000000000000000000000000000000) ((16551377117201082661994496 : ℝ) / 14551915228366851806640625) (-66) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_5_2 :
    (shellWeights ⟨5, by decide⟩ ⟨2, by decide⟩ : ℝ)^p ≤ powerUpper ⟨5, by decide⟩ ⟨2, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (23912895762421 : ℝ) / 500000000000000000000000)
    (by norm_num : 0 < (15414671150223429 : ℝ) / 1000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_5_2.2 power_upper_log_5_2.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_5_3 :
    (-36697320932978909649 : ℝ) / 1000000000000000000 ≤ Real.log ((577465472857 : ℝ) / 5000000000000000000000000000) ∧
    Real.log ((577465472857 : ℝ) / 5000000000000000000000000000) ≤ (-18348660466489454823 : ℝ) / 500000000000000000 := by
  have hb : (1973981834909587553 : ℝ) / 50000000000000000000 ≤ Real.log ((260067328837811247 : ℝ) / 250000000000000000) ∧
      Real.log ((260067328837811247 : ℝ) / 250000000000000000) ≤ (3947963669819175107 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((260067328837811247 : ℚ) / 250000000000000000) 25
      ((1973981834909587553 : ℚ) / 50000000000000000000)
      ((3947963669819175107 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (38753051882656104448 : ℝ) / 37252902984619140625) (l := (260067328837811247 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((577465472857 : ℝ) / 5000000000000000000000000000) ((38753051882656104448 : ℝ) / 37252902984619140625) (-53) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_5_3 :
    (-14089649900574850749 : ℝ) / 200000000000000000 ≤ Real.log ((634824953939609 : ℝ) / 2500000000000000000000000000000000000000000000) ∧
    Real.log ((634824953939609 : ℝ) / 2500000000000000000000000000000000000000000000) ≤ (-70448249502874253743 : ℝ) / 1000000000000000000 := by
  have hb : (6319072856004195399 : ℝ) / 25000000000000000000 ≤ Real.log ((1287577974242245491 : ℝ) / 1000000000000000000) ∧
      Real.log ((1287577974242245491 : ℝ) / 1000000000000000000) ≤ (25276291424016781597 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1287577974242245491 : ℚ) / 1000000000000000000) 25
      ((6319072856004195399 : ℚ) / 25000000000000000000)
      ((25276291424016781597 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (182975835264506584259881752068096 : ℝ) / 142108547152020037174224853515625) (l := (1287577974242245491 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((634824953939609 : ℝ) / 2500000000000000000000000000000000000000000000) ((182975835264506584259881752068096 : ℝ) / 142108547152020037174224853515625) (-102) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_5_3 :
    (shellWeights ⟨5, by decide⟩ ⟨3, by decide⟩ : ℝ)^p ≤ powerUpper ⟨5, by decide⟩ ⟨3, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (577465472857 : ℝ) / 5000000000000000000000000000)
    (by norm_num : 0 < (634824953939609 : ℝ) / 2500000000000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_5_3.2 power_upper_log_5_3.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_5_4 :
    (-49631169850584757229 : ℝ) / 1000000000000000000 ≤ Real.log ((27890532331439 : ℝ) / 100000000000000000000000000000000000) ∧
    Real.log ((27890532331439 : ℝ) / 100000000000000000000000000000000000) ≤ (-49631169850584757227 : ℝ) / 1000000000000000000 := by
  have hb : (27542714973130504937 : ℝ) / 100000000000000000000 ≤ Real.log ((1317093150713797163 : ℝ) / 1000000000000000000) ∧
      Real.log ((1317093150713797163 : ℝ) / 1000000000000000000) ≤ (13771357486565252469 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1317093150713797163 : ℚ) / 1000000000000000000) 25
      ((27542714973130504937 : ℚ) / 100000000000000000000)
      ((13771357486565252469 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (3833245575409956403806208 : ℝ) / 2910383045673370361328125) (l := (1317093150713797163 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((27890532331439 : ℝ) / 100000000000000000000000000000000000) ((3833245575409956403806208 : ℝ) / 2910383045673370361328125) (-72) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_5_4 :
    (-9527750113255211681 : ℝ) / 100000000000000000 ≤ Real.log ((2091592196895023 : ℝ) / 500000000000000000000000000000000000000000000000000000000) ∧
    Real.log ((2091592196895023 : ℝ) / 500000000000000000000000000000000000000000000000000000000) ≤ (-95277501132552116807 : ℝ) / 1000000000000000000 := by
  have hb : (18840489236016794533 : ℝ) / 50000000000000000000 ≤ Real.log ((1457627020068462559 : ℝ) / 1000000000000000000) ∧
      Real.log ((1457627020068462559 : ℝ) / 1000000000000000000) ≤ (37680978472033589067 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1457627020068462559 : ℚ) / 1000000000000000000) 25
      ((18840489236016794533 : ℚ) / 50000000000000000000)
      ((37680978472033589067 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (10114319243723514092393210249742167048192 : ℝ) / 6938893903907228377647697925567626953125) (l := (1457627020068462559 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((2091592196895023 : ℝ) / 500000000000000000000000000000000000000000000000000000000) ((10114319243723514092393210249742167048192 : ℝ) / 6938893903907228377647697925567626953125) (-138) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_5_4 :
    (shellWeights ⟨5, by decide⟩ ⟨4, by decide⟩ : ℝ)^p ≤ powerUpper ⟨5, by decide⟩ ⟨4, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (27890532331439 : ℝ) / 100000000000000000000000000000000000)
    (by norm_num : 0 < (2091592196895023 : ℝ) / 500000000000000000000000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_5_4.2 power_upper_log_5_4.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_5_5 :
    (-3910313673009565711 : ℝ) / 62500000000000000 ≤ Real.log ((67353099910173 : ℝ) / 100000000000000000000000000000000000000000) ∧
    Real.log ((67353099910173 : ℝ) / 100000000000000000000000000000000000000000) ≤ (-31282509384076525687 : ℝ) / 500000000000000000 := by
  have hb : (51137466280197178141 : ℝ) / 100000000000000000000 ≤ Real.log ((13340655863806673 : ℝ) / 8000000000000000) ∧
      Real.log ((13340655863806673 : ℝ) / 8000000000000000) ≤ (25568733140098589071 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((13340655863806673 : ℚ) / 8000000000000000) 25
      ((51137466280197178141 : ℚ) / 100000000000000000000)
      ((25568733140098589071 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (75832848914425727602447613952 : ℝ) / 45474735088646411895751953125) (l := (13340655863806673 : ℝ) / 8000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((67353099910173 : ℝ) / 100000000000000000000000000000000000000000) ((75832848914425727602447613952 : ℝ) / 45474735088646411895751953125) (-91) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_5_5 :
    (-120106752762157888123 : ℝ) / 1000000000000000000 ≤ Real.log ((68912822208367443 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000) ∧
    Real.log ((68912822208367443 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000) ≤ (-3002668819053947203 : ℝ) / 25000000000000000 := by
  have hb : (2504283276362978581 : ℝ) / 5000000000000000000 ≤ Real.log ((412533565401589461 : ℝ) / 250000000000000000) ∧
      Real.log ((412533565401589461 : ℝ) / 250000000000000000) ≤ (50085665527259571621 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((412533565401589461 : ℚ) / 250000000000000000) 25
      ((2504283276362978581 : ℚ) / 5000000000000000000)
      ((50085665527259571621 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (2795436173947463881839366988358212828995231154176 : ℝ) / 1694065894508600678136645001359283924102783203125) (l := (412533565401589461 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((68912822208367443 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000) ((2795436173947463881839366988358212828995231154176 : ℝ) / 1694065894508600678136645001359283924102783203125) (-174) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_5_5 :
    (shellWeights ⟨5, by decide⟩ ⟨5, by decide⟩ : ℝ)^p ≤ powerUpper ⟨5, by decide⟩ ⟨5, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (67353099910173 : ℝ) / 100000000000000000000000000000000000000000)
    (by norm_num : 0 < (68912822208367443 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_5_5.2 power_upper_log_5_5.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem residue_log_5 :
    (80154667420673023 : ℝ) / 7812500000000000 ≤ Real.log ((28561 : ℝ) / 1) ∧
    Real.log ((28561 : ℝ) / 1) ≤ (2051959485969229389 : ℝ) / 200000000000000000 := by
  have hb : (55573690200691261237 : ℝ) / 100000000000000000000 ≤ Real.log ((28561 : ℝ) / 16384) ∧
      Real.log ((28561 : ℝ) / 16384) ≤ (27786845100345630619 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((28561 : ℚ) / 16384) 25
      ((55573690200691261237 : ℚ) / 100000000000000000000)
      ((27786845100345630619 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (28561 : ℝ) / 16384) (l := (28561 : ℝ) / 16384)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((28561 : ℝ) / 1) ((28561 : ℝ) / 16384) (14) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem energy_log_5 :
    (693220116235512857 : ℝ) / 1000000000000000000 ≤ Real.log ((2000145876670877199 : ℝ) / 1000000000000000000) ∧
    Real.log ((2000145876670877199 : ℝ) / 1000000000000000000) ≤ (693220116235512859 : ℝ) / 1000000000000000000 := by
  have hb : (1823391889188691 : ℝ) / 25000000000000000000 ≤ Real.log ((1000072938335438599 : ℝ) / 1000000000000000000) ∧
      Real.log ((1000072938335438599 : ℝ) / 1000000000000000000) ≤ (1458713511350953 : ℝ) / 20000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1000072938335438599 : ℚ) / 1000000000000000000) 25
      ((1823391889188691 : ℚ) / 25000000000000000000)
      ((1458713511350953 : ℚ) / 20000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (2000145876670877199 : ℝ) / 2000000000000000000) (l := (1000072938335438599 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((2000145876670877199 : ℝ) / 1000000000000000000) ((2000145876670877199 : ℝ) / 2000000000000000000) (1) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem mass_log_5 :
    (26591143070617 : ℝ) / 1000000000000000000 ≤ Real.log ((250006647874154549 : ℝ) / 250000000000000000) ∧
    Real.log ((250006647874154549 : ℝ) / 250000000000000000) ≤ (26591143070619 : ℝ) / 1000000000000000000 := by
  have hb : (332389288382717 : ℝ) / 12500000000000000000 ≤ Real.log ((250006647874154549 : ℝ) / 250000000000000000) ∧
      Real.log ((250006647874154549 : ℝ) / 250000000000000000) ≤ (2659114307061737 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((250006647874154549 : ℚ) / 250000000000000000) 25
      ((332389288382717 : ℚ) / 12500000000000000000)
      ((2659114307061737 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (250006647874154549 : ℝ) / 250000000000000000) (l := (250006647874154549 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((250006647874154549 : ℝ) / 250000000000000000) ((250006647874154549 : ℝ) / 250000000000000000) (0) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

end UnitDistance.Witness.FiniteCertificates
