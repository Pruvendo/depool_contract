Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import omega.Omega.
Require Import Setoid.
Require Import ZArith.
Require Import FinProof.Common.
Require Import FinProof.CommonInstances.
Require Import FinProof.StateMonad2.
Require Import FinProof.StateMonadInstances.
Require Import FinProof.ProgrammingWith. 
Local Open Scope struct_scope.
Require Import FinProof.CommonProofs.
Require Import depoolContract.ProofEnvironment.
Require Import depoolContract.DePoolClass.
Require Import depoolContract.SolidityNotations.
Require Import depoolContract.DePoolFunc.
Require Import depoolContract.DePoolConsts.

Require Import depoolContract.Lib.CommonModelProofs.
Module CommonModelProofs := CommonModelProofs StateMonadSig.
Import CommonModelProofs. 
Require Import depoolContract.Lib.Tactics.
Require Import depoolContract.Lib.ErrorValueProofs.
Import DePoolSpec.LedgerClass.SolidityNotations. 
Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.
Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100.

Module ScenarioCommon  (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Import dc.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.




Record NetParams := NetParamsC {
    NetParams_ι_validatorsElectedFor : Z ;
    NetParams_ι_electionsStartBefore : Z ;
    NetParams_ι_electionsEndBefore : Z ;
    NetParams_ι_stakeHeldFor : Z ;

NetParams_ι_curValidatorData :  TvmCell;
    NetParams_ι_unknown34 : Z ; 
    NetParams_ι_utime_since : Z ;
    NetParams_ι_utime_until : Z ;
    NetParams_ι_prevValidatorData : TvmCell ;

NetParams_ι_rawConfigParam_17 : TvmCell ;
    NetParams_ι_unknown17_1 : Z ; 
    NetParams_ι_unknown17_2 : Z ; 
    NetParams_ι_unknown17_3 : Z ; 
    NetParams_ι_maxStakeFactor : Z;

NetParams_ι_rawConfigParam_1 : TvmCell ;
    NetParams_ι_electorRawAddress: Z ;

}.

Definition withNetParams (l : Ledger) (p : NetParams):= 
    {$ l With     (VMState_ι_validatorsElectedFor , NetParams_ι_validatorsElectedFor  p) ;
                  (VMState_ι_electionsStartBefore, NetParams_ι_electionsStartBefore p) ;
                  (VMState_ι_electionsEndBefore, NetParams_ι_electionsEndBefore p) ;
                  (VMState_ι_stakeHeldFor, NetParams_ι_stakeHeldFor p) ;

                  (VMState_ι_curValidatorData, NetParams_ι_curValidatorData p);
                  (VMState_ι_unknown34, NetParams_ι_unknown34 p) ; 
                  (VMState_ι_utime_since, NetParams_ι_utime_since p) ;
                  (VMState_ι_utime_until, NetParams_ι_utime_until p) ;

(* NetParams_ι_rawConfigParam_32 : C ; *)
                  (VMState_ι_prevValidatorData, NetParams_ι_prevValidatorData p) ;

                  (VMState_ι_rawConfigParam_17, NetParams_ι_rawConfigParam_17 p) ;
                  (VMState_ι_unknown17_1, NetParams_ι_unknown17_1 p) ; (*check the type*)
                  (VMState_ι_unknown17_2, NetParams_ι_unknown17_2 p) ; 
                  (VMState_ι_unknown17_3, NetParams_ι_unknown17_3 p) ; 
                  (VMState_ι_maxStakeFactor, NetParams_ι_maxStakeFactor p);

                  (VMState_ι_rawConfigParam_1, NetParams_ι_rawConfigParam_1 p) ;
                  (VMState_ι_electorRawAddress, NetParams_ι_electorRawAddress p) $} .

 
Definition DePoolContract_Ф_addOrdinaryStake'' ( Л_stake : XInteger64 ) : LedgerT ( XErrorValue True XInteger ) := 
           do r ← DePoolContract_Ф_addOrdinaryStake' Л_stake ; 
           return! (xErrorMapDefaultF (fun vv => xErrorMapDefaultF xValue vv (fun _ => xError xInt0)) r xError). 
                   
Definition DePoolContract_Ф_participateInElections'' ( Л_queryId : XInteger64 ) 
           ( Л_validatorKey : XInteger256 ) 
           ( Л_stakeAt : XInteger32 ) 
           ( Л_maxFactor : XInteger32 ) 
           ( Л_adnlAddr : XInteger256 ) 
           ( Л_signature : XList XInteger8 ) 
            : LedgerT ( XErrorValue True XInteger ) := 
do r ← DePoolContract_Ф_participateInElections' Л_queryId Л_validatorKey Л_stakeAt Л_maxFactor Л_adnlAddr Л_signature; 
return! (xErrorMapDefaultF (fun vv => xErrorMapDefaultF xValue vv (fun _ => xError xInt0)) r xError).       

Definition DePoolContract_Ф_addVestingOrLock'' ( Л_stake : XInteger64 ) 
           ( Л_beneficiary : XAddress ) 
                                 ( Л_withdrawalPeriod : XInteger32 ) 
                                 ( Л_totalPeriod : XInteger32 ) 
                                 ( Л_isVesting : XBool ) : LedgerT (XErrorValue True XInteger) := 
do r ← DePoolContract_Ф_addVestingOrLock' Л_stake Л_beneficiary Л_withdrawalPeriod Л_totalPeriod Л_isVesting ; 
return! (xErrorMapDefaultF (fun v => xValue v)  r (fun _ => xError xInt0)). 

End ScenarioCommon.