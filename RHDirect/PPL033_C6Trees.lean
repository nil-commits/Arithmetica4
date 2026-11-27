/-
Copyright 2026 Antigravity / Arithmetica4 Prize Campaign Contributors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
-/

import RHDirect.PPL033_C6Tree_00
import RHDirect.PPL033_C6Tree_01
import RHDirect.PPL033_C6Tree_02
import RHDirect.PPL033_C6Tree_03
import RHDirect.PPL033_C6Tree_04
import RHDirect.PPL033_C6Tree_05
import RHDirect.PPL033_C6Tree_06
import RHDirect.PPL033_C6Tree_07
import RHDirect.PPL033_C6Tree_08
import RHDirect.PPL033_C6Tree_09
import RHDirect.PPL033_C6Tree_10
import RHDirect.PPL033_C6Tree_11
import RHDirect.PPL033_C6Tree_12
import RHDirect.PPL033_C6Tree_13
import RHDirect.PPL033_C6Tree_14
import RHDirect.PPL033_C6Tree_15
import RHDirect.PPL033_C6Tree_16
import RHDirect.PPL033_C6Tree_17
import RHDirect.PPL033_C6Tree_18
import RHDirect.PPL033_C6Tree_19
import RHDirect.PPL033_C6Tree_20
import RHDirect.PPL033_C6Tree_21
import RHDirect.PPL033_C6Tree_22
import RHDirect.PPL033_C6Tree_23
import RHDirect.PPL033_C6Tree_24
import RHDirect.PPL033_C6Tree_25
import RHDirect.PPL033_C6Tree_26
import RHDirect.PPL033_C6Tree_27
import Mathlib.Tactic.FinCases

/-!
# PPL 033 — `C_6` Exact Branch-and-Bound Aggregator (all 116 `Q_3` root orbits)

Zero `sorry`, zero custom axioms, zero `native_decide`.
-/

namespace PPL033_C6Cert

theorem root_bound_0 (g : Q4Bits) (hc : isQ4C6Free g)
    (hf : extractFacetQ3 6 g = q3RepBits 0)
    (hmax : ∀ fk : Fin 8, evalQ3Fast (extractFacetQ3 fk g) ≤ evalQ3Fast (extractFacetQ3 6 g)) :
    q4ScoreGauged g ≤ M_target :=
  checkRoot_sound 0 12545968 436415616 (.branch 19 (.branch 18 sub_0_oo sub_0_oz) (.branch 18 sub_0_zo sub_0_zz))
    (checkRoot_of_branch2 0 12545968 436415616 19 18 18 _ _ _ _ _ _ sub_0_oo sub_0_oz sub_0_zo sub_0_zz
      sub_0_oo_ok sub_0_oz_ok sub_0_zo_ok sub_0_zz_ok rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) g hc hf hmax

theorem root_bound_1 (g : Q4Bits) (hc : isQ4C6Free g)
    (hf : extractFacetQ3 6 g = q3RepBits 1)
    (hmax : ∀ fk : Fin 8, evalQ3Fast (extractFacetQ3 fk g) ≤ evalQ3Fast (extractFacetQ3 6 g)) :
    q4ScoreGauged g ≤ M_target :=
  checkRoot_sound 1 12545948 436415456 (.branch 19 sub_1_o sub_1_z)
    (checkRoot_of_branch1 1 12545948 436415456 19 _ _ _ _ sub_1_o sub_1_z sub_1_o_ok sub_1_z_ok rfl rfl rfl rfl rfl rfl rfl) g hc hf hmax

theorem root_bound_3 (g : Q4Bits) (hc : isQ4C6Free g)
    (hf : extractFacetQ3 6 g = q3RepBits 3)
    (hmax : ∀ fk : Fin 8, evalQ3Fast (extractFacetQ3 fk g) ≤ evalQ3Fast (extractFacetQ3 6 g)) :
    q4ScoreGauged g ≤ M_target :=
  checkRoot_sound 3 12545962 436415568 (.branch 19 sub_3_o sub_3_z)
    (checkRoot_of_branch1 3 12545962 436415568 19 _ _ _ _ sub_3_o sub_3_z sub_3_o_ok sub_3_z_ok rfl rfl rfl rfl rfl rfl rfl) g hc hf hmax

theorem root_bound_36 (g : Q4Bits) (hc : isQ4C6Free g)
    (hf : extractFacetQ3 6 g = q3RepBits 36)
    (hmax : ∀ fk : Fin 8, evalQ3Fast (extractFacetQ3 fk g) ≤ evalQ3Fast (extractFacetQ3 6 g)) :
    q4ScoreGauged g ≤ M_target :=
  checkRoot_sound 36 12545956 436415520 (.branch 19 sub_36_o sub_36_z)
    (checkRoot_of_branch1 36 12545956 436415520 19 _ _ _ _ sub_36_o sub_36_z sub_36_o_ok sub_36_z_ok rfl rfl rfl rfl rfl rfl rfl) g hc hf hmax

theorem root_bound_106 (g : Q4Bits) (hc : isQ4C6Free g)
    (hf : extractFacetQ3 6 g = q3RepBits 106)
    (hmax : ∀ fk : Fin 8, evalQ3Fast (extractFacetQ3 fk g) ≤ evalQ3Fast (extractFacetQ3 6 g)) :
    q4ScoreGauged g ≤ M_target :=
  checkRoot_sound 106 12545960 436415552 (.branch 19 sub_106_o sub_106_z)
    (checkRoot_of_branch1 106 12545960 436415552 19 _ _ _ _ sub_106_o sub_106_z sub_106_o_ok sub_106_z_ok rfl rfl rfl rfl rfl rfl rfl) g hc hf hmax

theorem all_roots_bound (ri : Fin 116) (g : Q4Bits) (hc : isQ4C6Free g)
    (hf : extractFacetQ3 6 g = q3RepBits ri)
    (hmax : ∀ fk : Fin 8, evalQ3Fast (extractFacetQ3 fk g) ≤ evalQ3Fast (extractFacetQ3 6 g)) :
    q4ScoreGauged g ≤ M_target := by
  fin_cases ri
  · exact root_bound_0 g hc hf hmax
  · exact root_bound_1 g hc hf hmax
  · exact root_bound_2 g hc hf hmax
  · exact root_bound_3 g hc hf hmax
  · exact root_bound_4 g hc hf hmax
  · exact root_bound_5 g hc hf hmax
  · exact root_bound_6 g hc hf hmax
  · exact root_bound_7 g hc hf hmax
  · exact root_bound_8 g hc hf hmax
  · exact root_bound_9 g hc hf hmax
  · exact root_bound_10 g hc hf hmax
  · exact root_bound_11 g hc hf hmax
  · exact root_bound_12 g hc hf hmax
  · exact root_bound_13 g hc hf hmax
  · exact root_bound_14 g hc hf hmax
  · exact root_bound_15 g hc hf hmax
  · exact root_bound_16 g hc hf hmax
  · exact root_bound_17 g hc hf hmax
  · exact root_bound_18 g hc hf hmax
  · exact root_bound_19 g hc hf hmax
  · exact root_bound_20 g hc hf hmax
  · exact root_bound_21 g hc hf hmax
  · exact root_bound_22 g hc hf hmax
  · exact root_bound_23 g hc hf hmax
  · exact root_bound_24 g hc hf hmax
  · exact root_bound_25 g hc hf hmax
  · exact root_bound_26 g hc hf hmax
  · exact root_bound_27 g hc hf hmax
  · exact root_bound_28 g hc hf hmax
  · exact root_bound_29 g hc hf hmax
  · exact root_bound_30 g hc hf hmax
  · exact root_bound_31 g hc hf hmax
  · exact root_bound_32 g hc hf hmax
  · exact root_bound_33 g hc hf hmax
  · exact root_bound_34 g hc hf hmax
  · exact root_bound_35 g hc hf hmax
  · exact root_bound_36 g hc hf hmax
  · exact root_bound_37 g hc hf hmax
  · exact root_bound_38 g hc hf hmax
  · exact root_bound_39 g hc hf hmax
  · exact root_bound_40 g hc hf hmax
  · exact root_bound_41 g hc hf hmax
  · exact root_bound_42 g hc hf hmax
  · exact root_bound_43 g hc hf hmax
  · exact root_bound_44 g hc hf hmax
  · exact root_bound_45 g hc hf hmax
  · exact root_bound_46 g hc hf hmax
  · exact root_bound_47 g hc hf hmax
  · exact root_bound_48 g hc hf hmax
  · exact root_bound_49 g hc hf hmax
  · exact root_bound_50 g hc hf hmax
  · exact root_bound_51 g hc hf hmax
  · exact root_bound_52 g hc hf hmax
  · exact root_bound_53 g hc hf hmax
  · exact root_bound_54 g hc hf hmax
  · exact root_bound_55 g hc hf hmax
  · exact root_bound_56 g hc hf hmax
  · exact root_bound_57 g hc hf hmax
  · exact root_bound_58 g hc hf hmax
  · exact root_bound_59 g hc hf hmax
  · exact root_bound_60 g hc hf hmax
  · exact root_bound_61 g hc hf hmax
  · exact root_bound_62 g hc hf hmax
  · exact root_bound_63 g hc hf hmax
  · exact root_bound_64 g hc hf hmax
  · exact root_bound_65 g hc hf hmax
  · exact root_bound_66 g hc hf hmax
  · exact root_bound_67 g hc hf hmax
  · exact root_bound_68 g hc hf hmax
  · exact root_bound_69 g hc hf hmax
  · exact root_bound_70 g hc hf hmax
  · exact root_bound_71 g hc hf hmax
  · exact root_bound_72 g hc hf hmax
  · exact root_bound_73 g hc hf hmax
  · exact root_bound_74 g hc hf hmax
  · exact root_bound_75 g hc hf hmax
  · exact root_bound_76 g hc hf hmax
  · exact root_bound_77 g hc hf hmax
  · exact root_bound_78 g hc hf hmax
  · exact root_bound_79 g hc hf hmax
  · exact root_bound_80 g hc hf hmax
  · exact root_bound_81 g hc hf hmax
  · exact root_bound_82 g hc hf hmax
  · exact root_bound_83 g hc hf hmax
  · exact root_bound_84 g hc hf hmax
  · exact root_bound_85 g hc hf hmax
  · exact root_bound_86 g hc hf hmax
  · exact root_bound_87 g hc hf hmax
  · exact root_bound_88 g hc hf hmax
  · exact root_bound_89 g hc hf hmax
  · exact root_bound_90 g hc hf hmax
  · exact root_bound_91 g hc hf hmax
  · exact root_bound_92 g hc hf hmax
  · exact root_bound_93 g hc hf hmax
  · exact root_bound_94 g hc hf hmax
  · exact root_bound_95 g hc hf hmax
  · exact root_bound_96 g hc hf hmax
  · exact root_bound_97 g hc hf hmax
  · exact root_bound_98 g hc hf hmax
  · exact root_bound_99 g hc hf hmax
  · exact root_bound_100 g hc hf hmax
  · exact root_bound_101 g hc hf hmax
  · exact root_bound_102 g hc hf hmax
  · exact root_bound_103 g hc hf hmax
  · exact root_bound_104 g hc hf hmax
  · exact root_bound_105 g hc hf hmax
  · exact root_bound_106 g hc hf hmax
  · exact root_bound_107 g hc hf hmax
  · exact root_bound_108 g hc hf hmax
  · exact root_bound_109 g hc hf hmax
  · exact root_bound_110 g hc hf hmax
  · exact root_bound_111 g hc hf hmax
  · exact root_bound_112 g hc hf hmax
  · exact root_bound_113 g hc hf hmax
  · exact root_bound_114 g hc hf hmax
  · exact root_bound_115 g hc hf hmax

end PPL033_C6Cert
