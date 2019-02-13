{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Lang.QdataStructures where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

name4 = "Lang.dataStructures.⊥"
d4 = ()
data T4
name6 = "Lang.dataStructures.⊤"
d6 = ()
data T6 = C8
name10 = "Lang.dataStructures.Bool"
d10 = ()
data T10 = C12 | C14
name16 = "Lang.dataStructures.ℕ"
d16 = ()
data T16 = C18 | C20 T16
name22 = "Lang.dataStructures.one"
d22 :: T16
d22 = coe (C20 (coe C18))
name24 = "Lang.dataStructures.two"
d24 :: T16
d24 = coe (C20 (coe d22))
name26 = "Lang.dataStructures.three"
d26 :: T16
d26 = coe (C20 (coe d24))
name28 = "Lang.dataStructures.four"
d28 :: T16
d28 = coe (C20 (coe d26))
name30 = "Lang.dataStructures.five"
d30 :: T16
d30 = coe (C20 (coe d28))
name32 = "Lang.dataStructures.six"
d32 :: T16
d32 = coe (C20 (coe d30))
name34 = "Lang.dataStructures.seven"
d34 :: T16
d34 = coe (C20 (coe d32))
name36 = "Lang.dataStructures.eight"
d36 :: T16
d36 = coe (C20 (coe d34))
name38 = "Lang.dataStructures.nine"
d38 :: T16
d38 = coe (C20 (coe d36))
name40 = "Lang.dataStructures.ten"
d40 :: T16
d40 = coe (C20 (coe d38))
name42 = "Lang.dataStructures.BinTree"
d42 = ()
data T42 = C44 | C46 T42 T42
name48 = "Lang.dataStructures.ℕBinTree"
d48 = ()
data T48 = C50 T16 | C52 T48 T48
name54 = "Lang.dataStructures.ℕNodeBinTree"
d54 = ()
data T54 = C56 T16 | C58 T16 T54 T54
name60 = "Lang.dataStructures.ℕMixedBinTree"
d60 = ()
data T60 = C62 T10 | C64 T16 T60 T60
name66 = "Lang.dataStructures.Vertex"
d66 = ()
newtype T66 = C72 T16
name68 = "Lang.dataStructures.EdgeTriple"
d68 = ()
data T68 = C74 T66 T66
name70 = "Lang.dataStructures.Graph"
d70 = ()
data T70 = C76 T68 | C78 T70 T68
name80 = "Lang.dataStructures.graph"
d80 :: T70
d80
  = coe
      (C78
         (coe
            (C78
               (coe
                  (C78
                     (coe (C76 (coe (C74 (coe (C72 (coe C18))) (coe (C72 (coe d34)))))))
                     (coe (C74 (coe (C72 (coe d22))) (coe (C72 (coe d26)))))))
               (coe (C74 (coe (C72 (coe d34))) (coe (C72 (coe d28)))))))
         (coe
            (C74 (coe (C72 (coe d38))) (coe (C72 (coe (C20 (coe d32))))))))
name84 = "Lang.dataStructures.List"
d84 a0 = ()
data T84 = C88 | C90 AgdaAny T84
name92 = "Lang.dataStructures.bunch"
d92 :: T84
d92
  = coe
      (C90
         (coe C14)
         (coe
            (C90
               (coe C14)
               (coe
                  (C90
                     (coe C12)
                     (coe (C90 (coe C14) (coe (C90 (coe C12) (coe C88))))))))))
name94 = "Lang.dataStructures.Fin"
d94 a0 = ()
data T94 = C98 | C102 T94
name104 = "Lang.dataStructures.fourFin"
d104 :: T94
d104
  = coe
      (\ v0 v1 -> C102 v1) erased
      (coe
         (\ v0 v1 -> C102 v1) erased
         (coe (\ v0 v1 -> C102 v1) erased (coe (\ v0 -> C98) erased)))
name108 = "Lang.dataStructures.Vec"
d108 a0 a1 = ()
data T108 = C112 | C116 AgdaAny T108
name118 = "Lang.dataStructures.vec1"
d118 :: T108
d118 = coe (\ v0 v1 v2 -> C116 v1 v2) erased C12 C112
name120 = "Lang.dataStructures.vec2"
d120 :: T108
d120 = coe (\ v0 v1 v2 -> C116 v1 v2) erased C14 d118
name122 = "Lang.dataStructures.vec3"
d122 :: T108
d122 = coe (\ v0 v1 v2 -> C116 v1 v2) erased C12 d120
name124 = "Lang.dataStructures.⟂"
d124 = ()
data T124
name130 = "Lang.dataStructures.BoolVec"
d130 a0 a1 a2 = ()
data T130 = C136 AgdaAny | C138 AgdaAny
name140 = "Lang.dataStructures.containsB"
d140 :: T130
d140 = coe (C136 (coe d26))
name142 = "Lang.dataStructures.containsA"
d142 :: T130
d142 = coe (C138 (coe d28))
