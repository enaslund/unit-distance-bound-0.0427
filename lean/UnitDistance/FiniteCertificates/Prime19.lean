module

public import UnitDistance.FiniteCertificates.LogEnclosureCompactRun20260920

@[expose] public section
set_option backward.privateInPublic true


namespace UnitDistance.Witness.FiniteCertificates

theorem power_bound_7_0 :
    (shellWeights ⟨7, by decide⟩ ⟨0, by decide⟩ : ℝ)^p ≤ powerUpper ⟨7, by decide⟩ ⟨0, by decide⟩ := by
  norm_num [shellWeights, powerUpper, Matrix.cons_val]

theorem weight_log_7_1 :
    (-3177971564385799363 : ℝ) / 250000000000000000 ≤ Real.log ((30150737786821 : ℝ) / 10000000000000000000) ∧
    Real.log ((30150737786821 : ℝ) / 10000000000000000000) ≤ (-12711886257543197451 : ℝ) / 1000000000000000000 := by
  have hb : (45791017309576342703 : ℝ) / 100000000000000000000 ≤ Real.log ((395191750319420211 : ℝ) / 250000000000000000) ∧
      Real.log ((395191750319420211 : ℝ) / 250000000000000000) ≤ (2861938581848521419 : ℝ) / 6250000000000000000 := by
    have h := log_enclosure_of_rat
      ((395191750319420211 : ℚ) / 250000000000000000) 25
      ((45791017309576342703 : ℚ) / 100000000000000000000)
      ((2861938581848521419 : ℚ) / 6250000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (30150737786821 : ℝ) / 19073486328125) (l := (395191750319420211 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((30150737786821 : ℝ) / 10000000000000000000) ((30150737786821 : ℝ) / 19073486328125) (-19) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_7_1 :
    (-24403147476598762371 : ℝ) / 1000000000000000000 ≤ Real.log ((5045192082396183 : ℝ) / 200000000000000000000000000) ∧
    Real.log ((5045192082396183 : ℝ) / 200000000000000000000000000) ≤ (-24403147476598762369 : ℝ) / 1000000000000000000 := by
  have hb : (27507551177963438423 : ℝ) / 50000000000000000000 ≤ Real.log ((216689349959297433 : ℝ) / 125000000000000000) ∧
      Real.log ((216689349959297433 : ℝ) / 125000000000000000) ≤ (55015102355926876847 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((216689349959297433 : ℚ) / 125000000000000000) 25
      ((27507551177963438423 : ℚ) / 50000000000000000000)
      ((55015102355926876847 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (2583138346186845696 : ℝ) / 1490116119384765625) (l := (216689349959297433 : ℝ) / 125000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((5045192082396183 : ℝ) / 200000000000000000000000000) ((2583138346186845696 : ℝ) / 1490116119384765625) (-36) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_7_1 :
    (shellWeights ⟨7, by decide⟩ ⟨1, by decide⟩ : ℝ)^p ≤ powerUpper ⟨7, by decide⟩ ⟨1, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (30150737786821 : ℝ) / 10000000000000000000)
    (by norm_num : 0 < (5045192082396183 : ℝ) / 200000000000000000000000000) witness_basic.2.2.1.le
    weight_log_7_1.2 power_upper_log_7_1.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_7_2 :
    (-13528456900286424181 : ℝ) / 500000000000000000 ≤ Real.log ((8877724088281 : ℝ) / 5000000000000000000000000) ∧
    Real.log ((8877724088281 : ℝ) / 5000000000000000000000000) ≤ (-676422845014321209 : ℝ) / 25000000000000000 := by
  have hb : (33448671091248200779 : ℝ) / 50000000000000000000 ≤ Real.log ((1952232172650409567 : ℝ) / 1000000000000000000) ∧
      Real.log ((1952232172650409567 : ℝ) / 1000000000000000000) ≤ (66897342182496401559 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1952232172650409567 : ℚ) / 1000000000000000000) 25
      ((33448671091248200779 : ℚ) / 50000000000000000000)
      ((66897342182496401559 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (581810525849583616 : ℝ) / 298023223876953125) (l := (1952232172650409567 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((8877724088281 : ℝ) / 5000000000000000000000000) ((581810525849583616 : ℝ) / 298023223876953125) (-40) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_7_2 :
    (-12985363547939164481 : ℝ) / 250000000000000000 ≤ Real.log ((27676620737127237 : ℝ) / 1000000000000000000000000000000000000000) ∧
    Real.log ((27676620737127237 : ℝ) / 1000000000000000000000000000000000000000) ≤ (-51941454191756657921 : ℝ) / 1000000000000000000 := by
  have hb : (2229217511962014143 : ℝ) / 50000000000000000000 ≤ Real.log ((1045593169024837101 : ℝ) / 1000000000000000000) ∧
      Real.log ((1045593169024837101 : ℝ) / 1000000000000000000) ≤ (4458435023924028287 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1045593169024837101 : ℚ) / 1000000000000000000) 25
      ((2229217511962014143 : ℚ) / 50000000000000000000)
      ((4458435023924028287 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (1901922894876110334493458432 : ℝ) / 1818989403545856475830078125) (l := (1045593169024837101 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((27676620737127237 : ℝ) / 1000000000000000000000000000000000000000) ((1901922894876110334493458432 : ℝ) / 1818989403545856475830078125) (-75) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_7_2 :
    (shellWeights ⟨7, by decide⟩ ⟨2, by decide⟩ : ℝ)^p ≤ powerUpper ⟨7, by decide⟩ ⟨2, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (8877724088281 : ℝ) / 5000000000000000000000000)
    (by norm_num : 0 < (27676620737127237 : ℝ) / 1000000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_7_2.2 power_upper_log_7_2.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_7_3 :
    (-4140194135514085253 : ℝ) / 100000000000000000 ≤ Real.log ((2613998524199 : ℝ) / 2500000000000000000000000000000) ∧
    Real.log ((2613998524199 : ℝ) / 2500000000000000000000000000000) ≤ (-2587621334696303283 : ℝ) / 62500000000000000 := by
  have hb : (4672236961396650889 : ℝ) / 25000000000000000000 ≤ Real.log ((1205494044623835429 : ℝ) / 1000000000000000000) ∧
      Real.log ((1205494044623835429 : ℝ) / 1000000000000000000) ≤ (18688947845586603557 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1205494044623835429 : ℚ) / 1000000000000000000) 25
      ((4672236961396650889 : ℚ) / 25000000000000000000)
      ((18688947845586603557 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (5613519086613484797952 : ℝ) / 4656612873077392578125) (l := (1205494044623835429 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((2613998524199 : ℝ) / 2500000000000000000000000000000) ((5613519086613484797952 : ℝ) / 4656612873077392578125) (-60) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_7_3 :
    (-79479760929064856823 : ℝ) / 1000000000000000000 ≤ Real.log ((30365357986368193 : ℝ) / 1000000000000000000000000000000000000000000000000000) ∧
    Real.log ((30365357986368193 : ℝ) / 1000000000000000000000000000000000000000000000000000) ≤ (-3973988046453242841 : ℝ) / 50000000000000000 := by
  have hb : (23216483532885376061 : ℝ) / 100000000000000000000 ≤ Real.log ((1261327623047240061 : ℝ) / 1000000000000000000) ∧
      Real.log ((1261327623047240061 : ℝ) / 1000000000000000000) ≤ (11608241766442688031 : ℝ) / 50000000000000000000 := by
    have h := log_enclosure_of_rat
      ((1261327623047240061 : ℚ) / 1000000000000000000) 25
      ((23216483532885376061 : ℚ) / 100000000000000000000)
      ((11608241766442688031 : ℚ) / 50000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (560141987481106467848116146314149888 : ℝ) / 444089209850062616169452667236328125) (l := (1261327623047240061 : ℝ) / 1000000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((30365357986368193 : ℝ) / 1000000000000000000000000000000000000000000000000000) ((560141987481106467848116146314149888 : ℝ) / 444089209850062616169452667236328125) (-115) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_7_3 :
    (shellWeights ⟨7, by decide⟩ ⟨3, by decide⟩ : ℝ)^p ≤ powerUpper ⟨7, by decide⟩ ⟨3, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (2613998524199 : ℝ) / 2500000000000000000000000000000)
    (by norm_num : 0 < (30365357986368193 : ℝ) / 1000000000000000000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_7_3.2 power_upper_log_7_3.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_7_4 :
    (-55746968909705338773 : ℝ) / 1000000000000000000 ≤ Real.log ((30787117133133 : ℝ) / 50000000000000000000000000000000000000) ∧
    Real.log ((30787117133133 : ℝ) / 50000000000000000000000000000000000000) ≤ (-55746968909705338771 : ℝ) / 1000000000000000000 := by
  have hb : (795905431300462581 : ℝ) / 2000000000000000000 ≤ Real.log ((744386816274888089 : ℝ) / 500000000000000000) ∧
      Real.log ((744386816274888089 : ℝ) / 500000000000000000) ≤ (39795271565023129051 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((744386816274888089 : ℚ) / 500000000000000000) 25
      ((795905431300462581 : ℚ) / 2000000000000000000)
      ((39795271565023129051 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (541612692377303093323235328 : ℝ) / 363797880709171295166015625) (l := (744386816274888089 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((30787117133133 : ℝ) / 50000000000000000000000000000000000000) ((541612692377303093323235328 : ℝ) / 363797880709171295166015625) (-81) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_7_4 :
    (-21403613533273260463 : ℝ) / 200000000000000000 ≤ Real.log ((33315301546536587 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000) ∧
    Real.log ((33315301546536587 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000) ≤ (-13377258458295787789 : ℝ) / 125000000000000000 := by
  have hb : (5246816505315258073 : ℝ) / 12500000000000000000 ≤ Real.log ((760786996225562251 : ℝ) / 500000000000000000) ∧
      Real.log ((760786996225562251 : ℝ) / 500000000000000000) ≤ (8394906408504412917 : ℝ) / 20000000000000000000 := by
    have h := log_enclosure_of_rat
      ((760786996225562251 : ℚ) / 500000000000000000) 25
      ((5246816505315258073 : ℚ) / 12500000000000000000)
      ((8394906408504412917 : ℚ) / 20000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (164969382821295170957618890397762186695933952 : ℝ) / 108420217248550443400745280086994171142578125) (l := (760786996225562251 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((33315301546536587 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000) ((164969382821295170957618890397762186695933952 : ℝ) / 108420217248550443400745280086994171142578125) (-155) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_7_4 :
    (shellWeights ⟨7, by decide⟩ ⟨4, by decide⟩ : ℝ)^p ≤ powerUpper ⟨7, by decide⟩ ⟨4, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (30787117133133 : ℝ) / 50000000000000000000000000000000000000)
    (by norm_num : 0 < (33315301546536587 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_7_4.2 power_upper_log_7_4.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem weight_log_7_5 :
    (-70091996464269838383 : ℝ) / 1000000000000000000 ≤ Real.log ((18130204982799 : ℝ) / 50000000000000000000000000000000000000000000) ∧
    Real.log ((18130204982799 : ℝ) / 50000000000000000000000000000000000000000000) ≤ (-70091996464269838381 : ℝ) / 1000000000000000000 := by
  have hb : (6090159528445831781 : ℝ) / 10000000000000000000 ≤ Real.log ((459655304574119757 : ℝ) / 250000000000000000) ∧
      Real.log ((459655304574119757 : ℝ) / 250000000000000000) ≤ (60901595284458317811 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((459655304574119757 : ℚ) / 250000000000000000) 25
      ((6090159528445831781 : ℚ) / 10000000000000000000)
      ((60901595284458317811 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (10451351603799588638883852582912 : ℝ) / 5684341886080801486968994140625) (l := (459655304574119757 : ℝ) / 250000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((18130204982799 : ℝ) / 50000000000000000000000000000000000000000000) ((10451351603799588638883852582912 : ℝ) / 5684341886080801486968994140625) (-102) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_upper_log_7_5 :
    (-134556374403667773433 : ℝ) / 1000000000000000000 ≤ Real.log ((36551827172098617 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000) ∧
    Real.log ((36551827172098617 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000) ≤ (-134556374403667773429 : ℝ) / 1000000000000000000 := by
  have hb : (60732580552156190483 : ℝ) / 100000000000000000000 ≤ Real.log ((917758151094137043 : ℝ) / 500000000000000000) ∧
      Real.log ((917758151094137043 : ℝ) / 500000000000000000) ≤ (15183145138039047621 : ℝ) / 25000000000000000000 := by
    have h := log_enclosure_of_rat
      ((917758151094137043 : ℚ) / 500000000000000000) 25
      ((60732580552156190483 : ℚ) / 100000000000000000000)
      ((15183145138039047621 : ℚ) / 25000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (48585711974245273948199794496838695551423285813051392 : ℝ) / 26469779601696885595885078146238811314105987548828125) (l := (917758151094137043 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((36551827172098617 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000) ((48585711974245273948199794496838695551423285813051392 : ℝ) / 26469779601696885595885078146238811314105987548828125) (-195) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem power_bound_7_5 :
    (shellWeights ⟨7, by decide⟩ ⟨5, by decide⟩ : ℝ)^p ≤ powerUpper ⟨7, by decide⟩ ⟨5, by decide⟩ := by
  have h := rpow_le_of_log_bounds (p := p) (by norm_num : 0 < (18130204982799 : ℝ) / 50000000000000000000000000000000000000000000)
    (by norm_num : 0 < (36551827172098617 : ℝ) / 1000000000000000000000000000000000000000000000000000000000000000000000000000) witness_basic.2.2.1.le
    weight_log_7_5.2 power_upper_log_7_5.1 (by norm_num [p, increment])
  norm_num [shellWeights, powerUpper, Matrix.cons_val] at h ⊢
  exact h

theorem residue_log_7 :
    (11777755916665761839 : ℝ) / 1000000000000000000 ≤ Real.log ((130321 : ℝ) / 1) ∧
    Real.log ((130321 : ℝ) / 1) ≤ (11777755916665761841 : ℝ) / 1000000000000000000 := by
  have hb : (8592512846332961117 : ℝ) / 12500000000000000000 ≤ Real.log ((130321 : ℝ) / 65536) ∧
      Real.log ((130321 : ℝ) / 65536) ≤ (68740102770663688937 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((130321 : ℚ) / 65536) 25
      ((8592512846332961117 : ℚ) / 12500000000000000000)
      ((68740102770663688937 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (130321 : ℝ) / 65536) (l := (130321 : ℝ) / 65536)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((130321 : ℝ) / 1) ((130321 : ℝ) / 65536) (16) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem energy_log_7 :
    (34657838237794773 : ℝ) / 50000000000000000 ≤ Real.log ((62500599015117419 : ℝ) / 31250000000000000) ∧
    Real.log ((62500599015117419 : ℝ) / 31250000000000000) ≤ (346578382377947731 : ℝ) / 500000000000000000 := by
  have hb : (479209797507563 : ℝ) / 50000000000000000000 ≤ Real.log ((62500599015117419 : ℝ) / 62500000000000000) ∧
      Real.log ((62500599015117419 : ℝ) / 62500000000000000) ≤ (958419595015127 : ℝ) / 100000000000000000000 := by
    have h := log_enclosure_of_rat
      ((62500599015117419 : ℚ) / 62500000000000000) 25
      ((479209797507563 : ℚ) / 50000000000000000000)
      ((958419595015127 : ℚ) / 100000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (62500599015117419 : ℝ) / 62500000000000000) (l := (62500599015117419 : ℝ) / 62500000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((62500599015117419 : ℝ) / 31250000000000000) ((62500599015117419 : ℝ) / 62500000000000000) (1) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

theorem mass_log_7 :
    (3287442227289 : ℝ) / 1000000000000000000 ≤ Real.log ((500001643723815467 : ℝ) / 500000000000000000) ∧
    Real.log ((500001643723815467 : ℝ) / 500000000000000000) ≤ (3287442227291 : ℝ) / 1000000000000000000 := by
  have hb : (328744222728987 : ℝ) / 100000000000000000000 ≤ Real.log ((500001643723815467 : ℝ) / 500000000000000000) ∧
      Real.log ((500001643723815467 : ℝ) / 500000000000000000) ≤ (82186055682247 : ℝ) / 25000000000000000000 := by
    have h := log_enclosure_of_rat
      ((500001643723815467 : ℚ) / 500000000000000000) 25
      ((328744222728987 : ℚ) / 100000000000000000000)
      ((82186055682247 : ℚ) / 25000000000000000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    norm_num at h ⊢ <;> exact h
  have hr := log_bounds_of_lower (x := (500001643723815467 : ℝ) / 500000000000000000) (l := (500001643723815467 : ℝ) / 500000000000000000)
    (ε := (1 : ℝ) / 1000000000000000000) (by norm_num) (by norm_num) (by norm_num) hb
  have hs := log_scale_two ((500001643723815467 : ℝ) / 500000000000000000) ((500001643723815467 : ℝ) / 500000000000000000) (0) (by norm_num) (by norm_num)
  have h2 := log_two_precise
  simp only [div_one] at h2
  rw [hs]
  norm_num at hr ⊢
  constructor <;> linarith [h2.1, h2.2]

end UnitDistance.Witness.FiniteCertificates
