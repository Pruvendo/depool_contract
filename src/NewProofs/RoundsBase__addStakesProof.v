Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import Setoid.
Require Import ZArith.
Require Import Psatz.


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

Require Import depoolContract.NewProofs.ProofHelpers.
Require Import depoolContract.DePoolFunc.

(* Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100. *)

Require Import depoolContract.Lib.CommonModelProofs.
Module CommonModelProofs := CommonModelProofs StateMonadSig.
Import CommonModelProofs. 
Require Import depoolContract.Lib.Tactics.
Require Import depoolContract.Lib.ErrorValueProofs.
Require Import depoolContract.Lib.CommonCommon.

(* Require Import MultiSigWallet.Proofs.tvmFunctionsProofs. *)

Import DePoolSpec.LedgerClass.SolidityNotations. 

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Require Import depoolContract.DePoolConsts.
Module RoundsBase_Ф__addStakes (dc : DePoolConstsTypesSig XTypesSig StateMonadSig).
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig dc.
Module ProofHelpers := ProofHelpers dc.

Import dc.
Import ProofHelpers.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.


Opaque hmapLookup Z.add Z.eqb hmapInsert. 

Lemma RoundsBase_Ф__addStakes'_eval : forall ( Л_round : RoundsBase_ι_Round ) 
                                             ( Л_participant : DePoolLib_ι_Participant ) 
                                             ( Л_participantAddress : XAddress ) 
                                             ( Л_stake : XInteger64 ) 
                                             ( Л_vesting: XMaybe RoundsBase_ι_InvestParams) 
                                             ( Л_lock: XMaybe RoundsBase_ι_InvestParams)                                           
                                             ( l: Ledger ) , 
let stakeZero := ( Л_stake =? 0 ) in
let oPart := ( hmapLookup Z.eqb Л_participantAddress (Л_round ->> RoundsBase_ι_Round_ι_stakes) ) in

let round_participantQty := if negb (isSome oPart) 
                            then Л_round ->> RoundsBase_ι_Round_ι_participantQty + 1
                            else Л_round ->> RoundsBase_ι_Round_ι_participantQty in
let participant_roundQty := if negb (isSome oPart) 
                            then Л_participant ->> DePoolLib_ι_Participant_ι_roundQty + 1
                            else Л_participant ->> DePoolLib_ι_Participant_ι_roundQty in
        
let participant_haveVesting := (isSome Л_vesting || Л_participant ->> DePoolLib_ι_Participant_ι_haveVesting)%bool in
let participant_haveLock := (isSome Л_lock || Л_participant ->> DePoolLib_ι_Participant_ι_haveLock)%bool in

let round_stake := Л_round ->> RoundsBase_ι_Round_ι_stake + Л_stake in
let round_stake := if ( isSome Л_vesting )
                   then round_stake + ( ( maybeGet Л_vesting ) ->> RoundsBase_ι_InvestParams_ι_remainingAmount )
                   else round_stake in
let round_stake := if ( isSome Л_lock )
                   then round_stake + ( ( maybeGet Л_lock ) ->> RoundsBase_ι_InvestParams_ι_remainingAmount )
                   else round_stake in

let sv := ( Л_round ->> RoundsBase_ι_Round_ι_stakes ) [ Л_participantAddress ] in
let sv_vesting := if ( isSome Л_vesting )
                  then Л_vesting
                  else sv ->> RoundsBase_ι_StakeValue_ι_vesting in
let sv_lock := if ( isSome Л_lock )
               then Л_lock
               else sv ->> RoundsBase_ι_StakeValue_ι_lock in

let sv_ordinary := ( sv ->> RoundsBase_ι_StakeValue_ι_ordinary ) + Л_stake in
let sv := {$ sv with ( RoundsBase_ι_StakeValue_ι_ordinary , sv_ordinary ) ;
                     ( RoundsBase_ι_StakeValue_ι_vesting , sv_vesting ) ;
                     ( RoundsBase_ι_StakeValue_ι_lock , sv_lock ) $} in
let participant := {$ Л_participant with 
                             ( DePoolLib_ι_Participant_ι_roundQty , participant_roundQty ) ;
                             ( DePoolLib_ι_Participant_ι_haveVesting , participant_haveVesting ) ;
                             ( DePoolLib_ι_Participant_ι_haveLock , participant_haveLock )
                            $} in
let round_stakes := Л_round ->> RoundsBase_ι_Round_ι_stakes in                            
let round := {$ Л_round with ( RoundsBase_ι_Round_ι_participantQty , round_participantQty ) ; 
                             ( RoundsBase_ι_Round_ι_stake ,          round_stake ) ; 
                             ( RoundsBase_ι_Round_ι_stakes ,         round_stakes [ Л_participantAddress ] ←  sv ) $} in

eval_state ( ↓ RoundsBase_Ф__addStakes' Л_round Л_participant Л_participantAddress Л_stake Л_vesting Л_lock ) l = 

if (stakeZero &&
      ( negb ( isSome Л_vesting ) ) &&  
        ( negb ( isSome Л_lock) ) )%bool
then Error ( Л_round , Л_participant)
else Value ( round , participant ) .
Proof.

  intros.
  destructLedger l. 
  compute.

  Time do 5 destructIf_solve.
  
  (*multiple && not equivalently destructed - so will need to use discriminate*)
  all: destruct Л_round; destruct Л_lock; destruct Л_vesting; destruct (Л_stake =? 0); destruct (hmapLookup Z.eqb Л_participantAddress RoundsBase_ι_Round_ι_stakes);  try discriminate.  
  all: enough (forall X Y (a b: X), a = b -> Value (B:=Y) a = Value b) as H100.
  all: try apply H100.
  all: try apply pairEq; compute; auto.
  all: try apply RoundEq; compute; auto.
  all: try  destruct Л_participant; auto.
  all: intros; congruence.
Qed.



Lemma RoundsBase_Ф__addStakes'_exec : forall (Л_round : RoundsBase_ι_Round ) 
                                             (Л_participant : DePoolLib_ι_Participant ) 
                                             (Л_participantAddress : Z ) 
                                             (Л_stake : Z ) 
                                             (Л_vesting: option RoundsBase_ι_InvestParams) 
                                             (Л_lock: option RoundsBase_ι_InvestParams) 
                                             (l: Ledger) ,                                            
exec_state (↓ RoundsBase_Ф__addStakes' Л_round Л_participant Л_participantAddress Л_stake Л_vesting Л_lock ) l = l.
Proof.
  intros.
  destructLedger l. 
  compute.
  Time repeat destructIf_solve.
Qed. 

Opaque RoundsBase_Ф__addStakes'.

Lemma RoundsBase_Ф__addStakes_exec : forall  (Л_round : RoundsBase_ι_Round ) 
                                             (Л_participant : DePoolLib_ι_Participant ) 
                                             (Л_participantAddress : Z ) 
                                             (Л_stake : Z ) 
                                             (Л_vesting: option RoundsBase_ι_InvestParams) 
                                             (Л_lock: option RoundsBase_ι_InvestParams) 
                                             (l: Ledger) ,                                            
exec_state (↓ RoundsBase_Ф__addStakes Л_round Л_participant Л_participantAddress Л_stake Л_vesting Л_lock ) l = l.
Proof.
  intros.
  
  assert (exec_state
  (↓ RoundsBase_Ф__addStakes Л_round Л_participant Л_participantAddress
       Л_stake Л_vesting Л_lock) l = exec_state
       (↓ RoundsBase_Ф__addStakes' Л_round Л_participant Л_participantAddress
            Л_stake Л_vesting Л_lock) l).
  unfold RoundsBase_Ф__addStakes.
  unfold callEmbeddedStateAdj.
  unfold fromValueValue.
  remember (RoundsBase_Ф__addStakes' Л_round Л_participant Л_participantAddress Л_stake Л_vesting Л_lock).
  setoid_rewrite runbind.
  setoid_rewrite exec_bind.
  rewrite eval_get.
  rewrite exec_get.
  remember (run l0 (injEmbed (T:=LocalState) DePoolFuncs.DePoolSpec.LedgerClass.local0 l)).  
  setoid_rewrite <- Heqp.
  destruct p.
  destruct x.
  auto. auto.
  rewrite H.
  rewrite RoundsBase_Ф__addStakes'_exec.
  auto.
Qed.  

Lemma RoundsBase_Ф__addStakes_eval : forall ( Л_round : RoundsBase_ι_Round ) 
                                            ( Л_participant : DePoolLib_ι_Participant ) 
                                            ( Л_participantAddress : XAddress ) 
                                            ( Л_stake : XInteger64 ) 
                                            ( Л_vesting: XMaybe RoundsBase_ι_InvestParams) 
                                            ( Л_lock: XMaybe RoundsBase_ι_InvestParams)                                           
                                            ( l: Ledger ) , 
let stakeZero := ( Л_stake =? 0 ) in
let oPart := ( hmapLookup Z.eqb Л_participantAddress (Л_round ->> RoundsBase_ι_Round_ι_stakes) ) in

let round_participantQty := if negb (isSome oPart) 
                            then Л_round ->> RoundsBase_ι_Round_ι_participantQty + 1
                            else Л_round ->> RoundsBase_ι_Round_ι_participantQty in
let participant_roundQty := if negb (isSome oPart) 
                            then Л_participant ->> DePoolLib_ι_Participant_ι_roundQty + 1
                            else Л_participant ->> DePoolLib_ι_Participant_ι_roundQty in
        
let participant_haveVesting := (isSome Л_vesting || Л_participant ->> DePoolLib_ι_Participant_ι_haveVesting)%bool in
let participant_haveLock := (isSome Л_lock || Л_participant ->> DePoolLib_ι_Participant_ι_haveLock)%bool in

let round_stake := Л_round ->> RoundsBase_ι_Round_ι_stake + Л_stake in
let round_stake := if ( isSome Л_vesting )
                   then round_stake + ( ( maybeGet Л_vesting ) ->> RoundsBase_ι_InvestParams_ι_remainingAmount )
                   else round_stake in
let round_stake := if ( isSome Л_lock )
                   then round_stake + ( ( maybeGet Л_lock ) ->> RoundsBase_ι_InvestParams_ι_remainingAmount )
                   else round_stake in

let sv := ( Л_round ->> RoundsBase_ι_Round_ι_stakes ) [ Л_participantAddress ] in
let sv_vesting := if ( isSome Л_vesting )
                  then Л_vesting
                  else sv ->> RoundsBase_ι_StakeValue_ι_vesting in
let sv_lock := if ( isSome Л_lock )
               then Л_lock
               else sv ->> RoundsBase_ι_StakeValue_ι_lock in

let sv_ordinary := ( sv ->> RoundsBase_ι_StakeValue_ι_ordinary ) + Л_stake in
let sv := {$ sv with ( RoundsBase_ι_StakeValue_ι_ordinary , sv_ordinary ) ;
                     ( RoundsBase_ι_StakeValue_ι_vesting , sv_vesting ) ;
                     ( RoundsBase_ι_StakeValue_ι_lock , sv_lock ) $} in
let participant := {$ Л_participant with 
                             ( DePoolLib_ι_Participant_ι_roundQty , participant_roundQty ) ;
                             ( DePoolLib_ι_Participant_ι_haveVesting , participant_haveVesting ) ;
                             ( DePoolLib_ι_Participant_ι_haveLock , participant_haveLock )
                            $} in
let round_stakes := Л_round ->> RoundsBase_ι_Round_ι_stakes in                            
let round := {$ Л_round with ( RoundsBase_ι_Round_ι_participantQty , round_participantQty ) ; 
                             ( RoundsBase_ι_Round_ι_stake ,          round_stake ) ; 
                             ( RoundsBase_ι_Round_ι_stakes ,         round_stakes [ Л_participantAddress ] ←  sv ) $} in

eval_state ( ↓ RoundsBase_Ф__addStakes Л_round Л_participant Л_participantAddress Л_stake Л_vesting Л_lock ) l = 

if (stakeZero &&
      ( negb ( isSome Л_vesting ) ) &&  
        ( negb ( isSome Л_lock) ) )%bool then  ( Л_round , Л_participant)
                                         else  ( round , participant ) .
Proof.
  intros.

  assert (eval_state (↓ RoundsBase_Ф__addStakes Л_round Л_participant Л_participantAddress Л_stake Л_vesting Л_lock ) l = 
          fromValueValue (eval_state (↓ RoundsBase_Ф__addStakes' Л_round Л_participant Л_participantAddress Л_stake Л_vesting Л_lock) l)).
  unfold RoundsBase_Ф__addStakes.
  unfold callEmbeddedStateAdj.
  remember (RoundsBase_Ф__addStakes' Л_round Л_participant Л_participantAddress Л_stake Л_vesting Л_lock).
  setoid_rewrite runbind.
  setoid_rewrite eval_bind2.
  rewrite eval_get.
  rewrite exec_get.
  remember (run l0 (injEmbed (T:=LocalState) DePoolFuncs.DePoolSpec.LedgerClass.local0 l)).
  setoid_rewrite <- Heqp.
  destruct p.
  destruct x.
  auto. auto.

  (**********************)
  rewrite H.
  rewrite RoundsBase_Ф__addStakes'_eval.
  rewrite if_fromValueValue.
  auto.
Qed.

End RoundsBase_Ф__addStakes.



