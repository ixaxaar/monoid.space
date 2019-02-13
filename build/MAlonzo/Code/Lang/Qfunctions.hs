{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types,
             PatternSynonyms #-}
module MAlonzo.Code.Lang.Qfunctions where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, eqFloat, add64, sub64,
                    mul64, quot64, rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Lang.QdataStructures

name4 = "Lang.functions.not"
d4 ::
  MAlonzo.Code.Lang.QdataStructures.T10 ->
  MAlonzo.Code.Lang.QdataStructures.T10
d4 v0
  = case coe v0 of
      MAlonzo.Code.Lang.QdataStructures.C12
        -> coe MAlonzo.Code.Lang.QdataStructures.C14
      MAlonzo.Code.Lang.QdataStructures.C14
        -> coe MAlonzo.Code.Lang.QdataStructures.C12
      _ -> MAlonzo.RTE.mazUnreachableError
name6 = "Lang.functions._∧_"
d6 ::
  MAlonzo.Code.Lang.QdataStructures.T10 ->
  MAlonzo.Code.Lang.QdataStructures.T10 ->
  MAlonzo.Code.Lang.QdataStructures.T10
d6 v0 v1
  = case coe v0 of
      MAlonzo.Code.Lang.QdataStructures.C12 -> coe v1
      MAlonzo.Code.Lang.QdataStructures.C14 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
name12 = "Lang.functions._∨_"
d12 ::
  MAlonzo.Code.Lang.QdataStructures.T10 ->
  MAlonzo.Code.Lang.QdataStructures.T10 ->
  MAlonzo.Code.Lang.QdataStructures.T10
d12 v0 v1
  = case coe v0 of
      MAlonzo.Code.Lang.QdataStructures.C12 -> coe v0
      MAlonzo.Code.Lang.QdataStructures.C14 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
name18 = "Lang.functions.notTrue"
d18 :: MAlonzo.Code.Lang.QdataStructures.T10
d18 = coe (d4 (coe MAlonzo.Code.Lang.QdataStructures.C12))
name20 = "Lang.functions.false₁"
d20 :: MAlonzo.Code.Lang.QdataStructures.T10
d20
  = coe
      (d6
         (coe MAlonzo.Code.Lang.QdataStructures.C12)
         (coe MAlonzo.Code.Lang.QdataStructures.C14))
name22 = "Lang.functions.true₁"
d22 :: MAlonzo.Code.Lang.QdataStructures.T10
d22
  = coe
      (d12
         (coe MAlonzo.Code.Lang.QdataStructures.C12)
         (coe (d12 (coe MAlonzo.Code.Lang.QdataStructures.C14) (coe d20))))
name24 = "Lang.functions._+_"
d24 ::
  MAlonzo.Code.Lang.QdataStructures.T16 ->
  MAlonzo.Code.Lang.QdataStructures.T16 ->
  MAlonzo.Code.Lang.QdataStructures.T16
d24 v0 v1
  = case coe v0 of
      MAlonzo.Code.Lang.QdataStructures.C18 -> coe v1
      MAlonzo.Code.Lang.QdataStructures.C20 v2
        -> coe
             (MAlonzo.Code.Lang.QdataStructures.C20
                (coe (d24 (coe v2) (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
name32 = "Lang.functions.eleven"
d32 :: MAlonzo.Code.Lang.QdataStructures.T16
d32
  = coe
      (d24
         (coe MAlonzo.Code.Lang.QdataStructures.d40)
         (coe MAlonzo.Code.Lang.QdataStructures.d22))
name34 = "Lang.functions.twelve"
d34 :: MAlonzo.Code.Lang.QdataStructures.T16
d34
  = coe (d24 (coe d32) (coe MAlonzo.Code.Lang.QdataStructures.d22))
name36 = "Lang.functions.thirteen"
d36 :: MAlonzo.Code.Lang.QdataStructures.T16
d36
  = coe (d24 (coe d34) (coe MAlonzo.Code.Lang.QdataStructures.d22))
name40 = "Lang.functions._++_"
d40 ::
  () ->
  MAlonzo.Code.Lang.QdataStructures.T84 ->
  MAlonzo.Code.Lang.QdataStructures.T84 ->
  MAlonzo.Code.Lang.QdataStructures.T84
d40 v0 v1 v2 = du40 v1 v2
du40 ::
  MAlonzo.Code.Lang.QdataStructures.T84 ->
  MAlonzo.Code.Lang.QdataStructures.T84 ->
  MAlonzo.Code.Lang.QdataStructures.T84
du40 v0 v1
  = case coe v0 of
      MAlonzo.Code.Lang.QdataStructures.C88 -> coe v1
      MAlonzo.Code.Lang.QdataStructures.C90 v2 v3
        -> coe
             (MAlonzo.Code.Lang.QdataStructures.C90
                (coe v2) (coe (du40 (coe v3) (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
name50 = "Lang.functions.length"
d50 ::
  MAlonzo.Code.Lang.QdataStructures.T84 ->
  MAlonzo.Code.Lang.QdataStructures.T16
d50 v0
  = case coe v0 of
      MAlonzo.Code.Lang.QdataStructures.C88
        -> coe MAlonzo.Code.Lang.QdataStructures.C18
      MAlonzo.Code.Lang.QdataStructures.C90 v1 v2
        -> coe
             (d24
                (coe MAlonzo.Code.Lang.QdataStructures.d22) (coe (d50 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
name60 = "Lang.functions.map"
d60 ::
  () ->
  () ->
  MAlonzo.Code.Lang.QdataStructures.T84 ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Lang.QdataStructures.T84
d60 v0 v1 v2 v3 = du60 v2 v3
du60 ::
  MAlonzo.Code.Lang.QdataStructures.T84 ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Lang.QdataStructures.T84
du60 v0 v1
  = case coe v0 of
      MAlonzo.Code.Lang.QdataStructures.C88 -> coe v0
      MAlonzo.Code.Lang.QdataStructures.C90 v2 v3
        -> coe
             (MAlonzo.Code.Lang.QdataStructures.C90
                (coe v1 v2) (coe (du60 (coe v3) (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
name70 = "Lang.functions.addOne"
d70 ::
  MAlonzo.Code.Lang.QdataStructures.T16 ->
  MAlonzo.Code.Lang.QdataStructures.T16
d70 v0
  = coe (d24 (coe v0) (coe MAlonzo.Code.Lang.QdataStructures.d22))
name74 = "Lang.functions.oneAdded"
d74 :: MAlonzo.Code.Lang.QdataStructures.T84
d74
  = coe
      (du60
         (coe
            (MAlonzo.Code.Lang.QdataStructures.C90
               (coe MAlonzo.Code.Lang.QdataStructures.d22)
               (coe
                  (MAlonzo.Code.Lang.QdataStructures.C90
                     (coe MAlonzo.Code.Lang.QdataStructures.d24)
                     (coe
                        (MAlonzo.Code.Lang.QdataStructures.C90
                           (coe MAlonzo.Code.Lang.QdataStructures.d26)
                           (coe
                              (MAlonzo.Code.Lang.QdataStructures.C90
                                 (coe MAlonzo.Code.Lang.QdataStructures.d28)
                                 (coe MAlonzo.Code.Lang.QdataStructures.C88)))))))))
         (coe d70))
