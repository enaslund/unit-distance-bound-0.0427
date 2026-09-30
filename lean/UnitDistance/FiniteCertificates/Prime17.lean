module

public import UnitDistance.FiniteCertificates.LogEnclosureCompactRun20260920

@[expose] public section
set_option backward.privateInPublic true


namespace UnitDistance.Witness.FiniteCertificates

theorem power_bound_6_0 :
    (shellWeights ⟨6, by decide⟩ ⟨0, by decide⟩ : ℝ)^p ≤ powerUpper ⟨6, by decide⟩ ⟨0, by decide⟩ := by
  norm_num [shellWeights, powerUpper, Matrix.cons_val]

theorem weight_log_6_1 :
    (-12169633135497942471 : ℝ) / 1000000000000000000 ≤ Real.log ((51855578363751 : ℝ) / 10000000000000000000) ∧
    Real.log ((51855578363751 : ℝ) / 10000000000000000000) ≤ (-12169633135497942469 : ℝ) / 1000000000000000000 := by
  have hb : (6140322291621461977 : ℝ) / 20000000000000000000 ≤ Real.log ((679681436729357107 : ℝ) / 500000000000000000) ∧
      Real.log ((679681436729357107 : ℝ) / 500000000000000000) ≤ (15350805729053654943 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((679681436729357107 : ℚ) / 500000000000000000) 25
      ((6140322291621461977 : ℚ) / 20000000000000000000)
      ((15350805729053654943 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (51855578363751 : ℝ) / 38146972656250) (l := (679681436729357107 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((51855578363751 : ℝ) / 10000000000000000000) ((51855578363751 : ℝ) / 38146972656250) (-18) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_6_1 :
    (-11681089105302280449 : ℝ) / 500000000000000000 ≤ Real.log ((35719463087990403 : ℝ) / 500000000000000000000000000) ∧
    Real.log ((35719463087990403 : ℝ) / 500000000000000000000000000) ≤ (-45629254317587033 : ℝ) / 1953125000000000 := by
  have hb : (2560324105419745279 : ℝ) / 12500000000000000000 ≤ Real.log ((1227311406348783609 : ℝ) / 1000000000000000000) ∧
      Real.log ((1227311406348783609 : ℝ) / 1000000000000000000) ≤ (20482592843357962233 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1227311406348783609 : ℚ) / 1000000000000000000) 25
      ((2560324105419745279 : ℚ) / 12500000000000000000)
      ((20482592843357962233 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (9144182550525543168 : ℝ) / 7450580596923828125) (l := (1227311406348783609 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((35719463087990403 : ℝ) / 500000000000000000000000000) ((9144182550525543168 : ℝ) / 7450580596923828125) (-34) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_6_1 :
    (shellWeights ⟨6, by decide⟩ ⟨1, by decide⟩ : ℝ)^p ≤ powerUpper ⟨6, by decide⟩ ⟨1, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (51855578363751 : ℝ) / 10000000000000000000)
    (by norm_num : 0 < (35719463087990403 : ℝ) / 500000000000000000000000000) witness_basic.2.2.1.le
    weight_log_6_1.2 power_upper_log_6_1.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_6_2 :
    (-13045820025536813703 : ℝ) / 500000000000000000 ≤ Real.log ((932340817081 : ℝ) / 200000000000000000000000) ∧
    Real.log ((932340817081 : ℝ) / 200000000000000000000000) ≤ (-6522910012768406851 : ℝ) / 250000000000000000 := by
  have hb : (24795281020429435209 : ℝ) / 100000000000000000000 ≤ Real.log ((640699730894210109 : ℝ) / 500000000000000000) ∧
      Real.log ((640699730894210109 : ℝ) / 500000000000000000) ≤ (2479528102042943521 : ℝ) / 10000000000000000000 := by
    have h := log_enclosure_of_rat
      ((640699730894210109 : ℚ) / 500000000000000000) 25
      ((24795281020429435209 : ℚ) / 100000000000000000000)
      ((2479528102042943521 : ℚ) / 10000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (15275471947055104 : ℝ) / 11920928955078125) (l := (640699730894210109 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((932340817081 : ℝ) / 200000000000000000000000) ((15275471947055104 : ℝ) / 11920928955078125) (-38) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_6_2 :
    (-50088407587414903373 : ℝ) / 1000000000000000000 ≤ Real.log ((110347117970817 : ℝ) / 625000000000000000000000000000000000) ∧
    Real.log ((110347117970817 : ℝ) / 625000000000000000000000000000000000) ≤ (-5008840758741490337 : ℝ) / 100000000000000000 := by
  have hb : (51133659346110421539 : ℝ) / 100000000000000000000 ≤ Real.log ((1667518500437276473 : ℝ) / 1000000000000000000) ∧
      Real.log ((1667518500437276473 : ℝ) / 1000000000000000000) ≤ (2556682967305521077 : ℝ) / 5000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1667518500437276473 : ℚ) / 1000000000000000000) 25
      ((51133659346110421539 : ℚ) / 100000000000000000000)
      ((2556682967305521077 : ℚ) / 5000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (121327939300483301734612992 : ℝ) / 72759576141834259033203125) (l := (1667518500437276473 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((110347117970817 : ℝ) / 625000000000000000000000000000000000) ((121327939300483301734612992 : ℝ) / 72759576141834259033203125) (-73) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_6_2 :
    (shellWeights ⟨6, by decide⟩ ⟨2, by decide⟩ : ℝ)^p ≤ powerUpper ⟨6, by decide⟩ ⟨2, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (932340817081 : ℝ) / 200000000000000000000000)
    (by norm_num : 0 < (110347117970817 : ℝ) / 625000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_6_2.2 power_upper_log_6_2.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_6_3 :
    (-8002729397390563841 : ℝ) / 200000000000000000 ≤ Real.log ((20953854169957 : ℝ) / 5000000000000000000000000000000) ∧
    Real.log ((20953854169957 : ℝ) / 5000000000000000000000000000000) ≤ (-40013646986952819203 : ℝ) / 1000000000000000000 := by
  have hb : (3777789710480174833 : ℝ) / 20000000000000000000 ≤ Real.log ((603953726923481977 : ℝ) / 500000000000000000) ∧
      Real.log ((603953726923481977 : ℝ) / 500000000000000000) ≤ (9444474276200437083 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((603953726923481977 : ℚ) / 500000000000000000) 25
      ((3777789710480174833 : ℚ) / 20000000000000000000)
      ((9444474276200437083 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (5624757399069908795392 : ℝ) / 4656612873077392578125) (l := (603953726923481977 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((20953854169957 : ℝ) / 5000000000000000000000000000000) ((5624757399069908795392 : ℝ) / 4656612873077392578125) (-58) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_6_3 :
    (-3072585480128084429 : ℝ) / 40000000000000000 ≤ Real.log ((43634200220289423 : ℝ) / 100000000000000000000000000000000000000000000000000) ∧
    Real.log ((43634200220289423 : ℝ) / 100000000000000000000000000000000000000000000000000) ≤ (-38407318501601055361 : ℝ) / 500000000000000000 := by
  have hb : (1247000389518186207 : ℝ) / 10000000000000000000 ≤ Real.log ((1132808603642442273 : ℝ) / 1000000000000000000) ∧
      Real.log ((1132808603642442273 : ℝ) / 1000000000000000000) ≤ (12470003895181862071 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1132808603642442273 : ℚ) / 1000000000000000000) 25
      ((1247000389518186207 : ℚ) / 10000000000000000000)
      ((12470003895181862071 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (100613615540584990668626724384669696 : ℝ) / 88817841970012523233890533447265625) (l := (1132808603642442273 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((43634200220289423 : ℝ) / 100000000000000000000000000000000000000000000000000) ((100613615540584990668626724384669696 : ℝ) / 88817841970012523233890533447265625) (-111) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_6_3 :
    (shellWeights ⟨6, by decide⟩ ⟨3, by decide⟩ : ℝ)^p ≤ powerUpper ⟨6, by decide⟩ ⟨3, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (20953854169957 : ℝ) / 5000000000000000000000000000000)
    (by norm_num : 0 < (43634200220289423 : ℝ) / 100000000000000000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_6_3.2 power_upper_log_6_3.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_6_4 :
    (-6741956740352793797 : ℝ) / 125000000000000000 ≤ Real.log ((9418530145547 : ℝ) / 2500000000000000000000000000000000000) ∧
    Real.log ((9418530145547 : ℝ) / 2500000000000000000000000000000000000) ≤ (-53935653922822350373 : ℝ) / 1000000000000000000 := by
  have hb : (3245654021334593993 : ℝ) / 25000000000000000000 ≤ Real.log ((569315213788524979 : ℝ) / 500000000000000000) ∧
      Real.log ((569315213788524979 : ℝ) / 500000000000000000) ≤ (12982616085338375973 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((569315213788524979 : ℚ) / 500000000000000000) 25
      ((3245654021334593993 : ℚ) / 25000000000000000000)
      ((12982616085338375973 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (82846267292701665343307776 : ℝ) / 72759576141834259033203125) (l := (569315213788524979 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((9418530145547 : ℝ) / 2500000000000000000000000000000000000) ((82846267292701665343307776 : ℝ) / 72759576141834259033203125) (-78) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_6_4 :
    (-20708173283794154491 : ℝ) / 200000000000000000 ≤ Real.log ((2156766148395401 : ℝ) / 2000000000000000000000000000000000000000000000000000000000000) ∧
    Real.log ((2156766148395401 : ℝ) / 2000000000000000000000000000000000000000000000000000000000000) ≤ (-25885216604742693113 : ℝ) / 250000000000000000 := by
  have hb : (8624213300420479169 : ℝ) / 20000000000000000000 ≤ Real.log ((1539119754501827977 : ℝ) / 1000000000000000000) ∧
      Real.log ((1539119754501827977 : ℝ) / 1000000000000000000) ≤ (21560533251051197923 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1539119754501827977 : ℚ) / 1000000000000000000) 25
      ((8624213300420479169 : ℚ) / 20000000000000000000)
      ((21560533251051197923 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (1334973585236990508841421943622678884646912 : ℝ) / 867361737988403547205962240695953369140625) (l := (1539119754501827977 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((2156766148395401 : ℝ) / 2000000000000000000000000000000000000000000000000000000000000) ((1334973585236990508841421943622678884646912 : ℝ) / 867361737988403547205962240695953369140625) (-150) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_6_4 :
    (shellWeights ⟨6, by decide⟩ ⟨4, by decide⟩ : ℝ)^p ≤ powerUpper ⟨6, by decide⟩ ⟨4, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (9418530145547 : ℝ) / 2500000000000000000000000000000000000)
    (by norm_num : 0 < (2156766148395401 : ℝ) / 2000000000000000000000000000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_6_4.2 power_upper_log_6_4.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_6_5 :
    (-33928830429345943983 : ℝ) / 500000000000000000 ≤ Real.log ((33868217038473 : ℝ) / 10000000000000000000000000000000000000000000) ∧
    Real.log ((33868217038473 : ℝ) / 10000000000000000000000000000000000000000000) ≤ (-67857660858691887963 : ℝ) / 1000000000000000000 := by
  have hb : (3538141809137617903 : ℝ) / 50000000000000000000 ≤ Real.log ((107332664143700611 : ℝ) / 100000000000000000) ∧
      Real.log ((107332664143700611 : ℝ) / 100000000000000000) ≤ (7076283618275235807 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((107332664143700611 : ℚ) / 100000000000000000) 25
      ((3538141809137617903 : ℚ) / 50000000000000000000)
      ((7076283618275235807 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (1220231117073360691115656740864 : ℝ) / 1136868377216160297393798828125) (l := (107332664143700611 : ℝ) / 100000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((33868217038473 : ℝ) / 10000000000000000000000000000000000000000000) ((1220231117073360691115656740864 : ℝ) / 1136868377216160297393798828125) (-98) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_6_5 :
    (-65133547917369723253 : ℝ) / 500000000000000000 ≤ Real.log ((13325671707571811 : ℝ) / 5000000000000000000000000000000000000000000000000000000000000000000000000) ∧
    Real.log ((13325671707571811 : ℝ) / 5000000000000000000000000000000000000000000000000000000000000000000000000) ≤ (-65133547917369723251 : ℝ) / 500000000000000000 := by
  have hb : (2228705526513583257 : ℝ) / 50000000000000000000 ≤ Real.log ((261395615627475651 : ℝ) / 250000000000000000) ∧
      Real.log ((261395615627475651 : ℝ) / 250000000000000000) ≤ (891482210605433303 : ℝ) / 20000000000000000000 := by
    have h := log_enclosure_of_rat
      ((261395615627475651 : ℚ) / 250000000000000000) 25
      ((2228705526513583257 : ℚ) / 50000000000000000000)
      ((891482210605433303 : ℚ) / 20000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (1107053493521464743401702387872851876472504709021696 : ℝ) / 1058791184067875423835403125849552452564239501953125) (l := (261395615627475651 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((13325671707571811 : ℝ) / 5000000000000000000000000000000000000000000000000000000000000000000000000) ((1107053493521464743401702387872851876472504709021696 : ℝ) / 1058791184067875423835403125849552452564239501953125) (-188) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_6_5 :
    (shellWeights ⟨6, by decide⟩ ⟨5, by decide⟩ : ℝ)^p ≤ powerUpper ⟨6, by decide⟩ ⟨5, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (33868217038473 : ℝ) / 10000000000000000000000000000000000000000000)
    (by norm_num : 0 < (13325671707571811 : ℝ) / 5000000000000000000000000000000000000000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_6_5.2 power_upper_log_6_5.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem residue_log_6 :
    (35415166800702701 : ℝ) / 3125000000000000 ≤ Real.log ((83521 : ℝ) / 1) ∧
    Real.log ((83521 : ℝ) / 1) ≤ (5666426688112432161 : ℝ) / 500000000000000000 := by
  have hb : (3031231090821742129 : ℝ) / 12500000000000000000 ≤ Real.log ((83521 : ℝ) / 65536) ∧
      Real.log ((83521 : ℝ) / 65536) ≤ (24249848726573937033 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((83521 : ℚ) / 65536) 25
      ((3031231090821742129 : ℚ) / 12500000000000000000)
      ((24249848726573937033 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (83521 : ℝ) / 65536) (l := (83521 : ℝ) / 65536)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((83521 : ℝ) / 1) ((83521 : ℝ) / 65536) (16) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem energy_log_6 :
    (693164289110647631 : ℝ) / 1000000000000000000 ≤ Real.log ((2000034217394108821 : ℝ) / 1000000000000000000) ∧
    Real.log ((2000034217394108821 : ℝ) / 1000000000000000000) ≤ (693164289110647633 : ℝ) / 1000000000000000000 := by
  have hb : (1710855070232181 : ℝ) / 100000000000000000000 ≤ Real.log ((100001710869705441 : ℝ) / 100000000000000000) ∧
      Real.log ((100001710869705441 : ℝ) / 100000000000000000) ≤ (855427535116091 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((100001710869705441 : ℚ) / 100000000000000000) 25
      ((1710855070232181 : ℚ) / 100000000000000000000)
      ((855427535116091 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (2000034217394108821 : ℝ) / 2000000000000000000) (l := (100001710869705441 : ℝ) / 100000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((2000034217394108821 : ℝ) / 1000000000000000000) ((2000034217394108821 : ℝ) / 2000000000000000000) (1) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem mass_log_6 :
    (5966562545841 : ℝ) / 1000000000000000000 ≤ Real.log ((1000005966580345811 : ℝ) / 1000000000000000000) ∧
    Real.log ((1000005966580345811 : ℝ) / 1000000000000000000) ≤ (5966562545843 : ℝ) / 1000000000000000000 := by
  have hb : (596656254584129 : ℝ) / 100000000000000000000 ≤ Real.log ((1000005966580345811 : ℝ) / 1000000000000000000) ∧
      Real.log ((1000005966580345811 : ℝ) / 1000000000000000000) ≤ (59665625458413 : ℝ) / 10000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1000005966580345811 : ℚ) / 1000000000000000000) 25
      ((596656254584129 : ℚ) / 100000000000000000000)
      ((59665625458413 : ℚ) / 10000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (1000005966580345811 : ℝ) / 1000000000000000000) (l := (1000005966580345811 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((1000005966580345811 : ℝ) / 1000000000000000000) ((1000005966580345811 : ℝ) / 1000000000000000000) (0) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

end UnitDistance.Witness.FiniteCertificates
