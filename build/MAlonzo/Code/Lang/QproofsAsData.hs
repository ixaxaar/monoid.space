{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Lang.QproofsAsData where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Lang.QdataStructures

name4 = "Lang.proofsAsData._<=_"
d4 a0 a1 = ()
data T4 = C8 | C14 T4
name16 = "Lang.proofsAsData.idLess₁"
d16 :: T4
d16
  = coe
      (\ v0 v1 v2 -> C14 v2) erased erased (coe (\ v0 -> C8) erased)
name18 = "Lang.proofsAsData.idLess₂"
d18 :: T4
d18
  = coe
      (\ v0 v1 v2 -> C14 v2) erased erased
      (coe
         (\ v0 v1 v2 -> C14 v2) erased erased (coe (\ v0 -> C8) erased))
name20 = "Lang.proofsAsData.idLess₃"
d20 :: T4
d20
  = coe
      (\ v0 v1 v2 -> C14 v2) erased erased
      (coe
         (\ v0 v1 v2 -> C14 v2) erased erased
         (coe
            (\ v0 v1 v2 -> C14 v2) erased erased (coe (\ v0 -> C8) erased)))
name22 = "Lang.proofsAsData.Even"
d22 a0 = ()
data T22 = C26 | C30 T22
name24 = "Lang.proofsAsData.Odd"
d24 a0 = ()
data T24 = C32 | C36 T24
name38 = "Lang.proofsAsData.twoisEven"
d38 :: T22
d38 = coe (\ v0 v1 -> C30 v1) erased C26
name40 = "Lang.proofsAsData.isFourEven"
d40 :: T22
d40
  = coe
      (\ v0 v1 -> C30 v1) erased (coe (\ v0 v1 -> C30 v1) erased C26)
name42 = "Lang.proofsAsData.isSevenOdd"
d42 :: T24
d42
  = coe
      (\ v0 v1 -> C36 v1) erased
      (coe
         (\ v0 v1 -> C36 v1) erased (coe (\ v0 v1 -> C36 v1) erased C32))
name44 = "Lang.proofsAsData._≡_"
d44 a0 a1 = ()
data T44 = C46 | C52
name54 = "Lang.proofsAsData._≠_"
d54 a0 a1 = ()
data T54 = C58 | C62 | C68
name74 = "Lang.proofsAsData._∈_"
d74 a0 a1 a2 = ()
data T74 = C82 | C88 T74
name90 = "Lang.proofsAsData.theList"
d90 :: MAlonzo.Code.Lang.QdataStructures.T84
d90
  = coe
      (MAlonzo.Code.Lang.QdataStructures.C90
         (coe MAlonzo.Code.Lang.QdataStructures.d22)
         (coe
            (MAlonzo.Code.Lang.QdataStructures.C90
               (coe MAlonzo.Code.Lang.QdataStructures.d24)
               (coe
                  (MAlonzo.Code.Lang.QdataStructures.C90
                     (coe MAlonzo.Code.Lang.QdataStructures.d28)
                     (coe
                        (MAlonzo.Code.Lang.QdataStructures.C90
                           (coe MAlonzo.Code.Lang.QdataStructures.d34)
                           (coe
                              (MAlonzo.Code.Lang.QdataStructures.C90
                                 (coe MAlonzo.Code.Lang.QdataStructures.d26)
                                 (coe MAlonzo.Code.Lang.QdataStructures.C88))))))))))
name92 = "Lang.proofsAsData.threeIsInList"
d92 :: T74
d92
  = coe
      (\ v0 v1 v2 -> C88 v2) erased erased
      (coe
         (\ v0 v1 v2 -> C88 v2) erased erased
         (coe
            (\ v0 v1 v2 -> C88 v2) erased erased
            (coe
               (\ v0 v1 v2 -> C88 v2) erased erased (coe (\ v0 -> C82) erased))))
