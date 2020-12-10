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
Module DePoolFuncs := DePoolFuncs XTypesSig StateMonadSig.
Import DePoolFuncs.
Import DePoolSpec.
Import LedgerClass.

(* Import SolidityNotations. *)
Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100.
(*Set Typeclasses Strict Resolution. *)
(* Set Typeclasses Debug.  *) 
(* Set Typeclasses Unique Instances. 
Unset Typeclasses Unique Solutions. *)

(* Existing Instance monadStateT.
Existing Instance monadStateStateT. *)
(* Module MultiSigWalletSpecSig := MultiSigWalletSpecSig XTypesSig StateMonadSig. *)

Require Import depoolContract.Lib.CommonModelProofs.
Module CommonModelProofs := CommonModelProofs StateMonadSig.
Import CommonModelProofs. 
Require Import depoolContract.Lib.Tactics.
Require Import depoolContract.Lib.ErrorValueProofs.
Require Import depoolContract.Lib.CommonCommon.

(* Require Import MultiSigWallet.Proofs.tvmFunctionsProofs. *)

Import DePoolSpec.LedgerClass.SolidityNotations. 

Local Open Scope solidity_scope.

(* Require Import MultiSigWallet.Specifications._validatelimit_inlineSpec.
Module _validatelimit_inlineSpec := _validatelimit_inlineSpec MultiSigWalletSpecSig.
Import _validatelimit_inlineSpec. *)

Local Open Scope struct_scope.
Local Open Scope Z_scope.
Local Open Scope solidity_scope.
Require Import Lists.List.
Import ListNotations.
Local Open Scope list_scope.

(* Existing Instance embeddedLocalState.
 
Existing Instance monadStateT.
Existing Instance monadStateStateT. *)

(* Existing Instance embeddedLocalState.
Existing Instance embeddedMultisig. *)


Opaque Z.eqb Z.add Z.sub Z.div Z.mul hmapLookup hmapInsert Z.ltb Z.geb Z.leb Z.gtb Z.modulo deleteListPair.

(* Opaque tvm_accept DePoolContract_Ф_checkPureDePoolBalance RoundsBase_Ф_getRound1. *)


Lemma ifSimpleState: forall X (b: bool) (f g: Ledger -> X * Ledger), 
(if b then SimpleState f else SimpleState g ) =
SimpleState (if b then f else  g).
Proof.
  intros. destruct b; auto.
Qed.  

Lemma ifFunApply: forall X (b: bool) (f g: Ledger -> X * Ledger) l, 
(if b then f else  g ) l =
(if b then f l else g l).
Proof.
  intros. destruct b; auto.
Qed. 

Lemma fstImplies : forall  X Y T (f: X*T) (g: X -> Y)  ,  (let (x, _) := f in g x) = g (fst f).
Proof.
  intros.
  destruct f; auto.
Qed.

Lemma sndImplies : forall  X Y T (f: X*T) (g: T -> Y)  ,  (let (_, t) := f in g t) = g (snd f).
Proof.
  intros.
  destruct f; auto.
Qed.

Lemma fstsndImplies : forall  X Y T (f: X*T) (g: X -> T -> Y)  ,  (let (x, t) := f in g x t) = g (fst f) (snd f).
Proof.
  intros.
  destruct f; auto.
Qed.


Lemma letIf: forall X Y (b: bool) (f g: X*Ledger) (h: X -> Ledger -> Y), 
(let (x, t) := if b then f else g in h x t)=
if b then let (x, t) := f in h x t else
          let (x, t) := g in h x t .
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma matchIf: forall X (b: bool) (f g: LedgerT X) (l: Ledger), 
(match (if b then f else g) with | SimpleState c => c end l)=
if b then match f with | SimpleState c => c end l else 
match g with | SimpleState c => c end l.
Proof.
  intros.
  destruct b; auto.
Qed.




Ltac pr_numgoals := let n := numgoals in idtac "There are" n "goals".
Ltac pr_hyp := repeat match goal with
               | H: ?x = true |- _ => idtac x " = true"
               | H: ?x = false |- _ => idtac x " = false"  
                end.


(* function completeRoundWithChunk(uint64 roundId, uint8 chunkSize) public selfCall {
req     require(msg.sender == address(this), Errors.IS_NOT_DEPOOL);
        tvm.accept();
        if (!(isRound2(roundId) || m_poolClosed))
            return;
        optional(Round) optRound = fetchRound(roundId);
        require(optRound.hasValue(), InternalErrors.ERROR519);
        Round round = optRound.get();
        if (round.step != RoundStep.Completing)
            return;
        round = _returnOrReinvest(round, chunkSize);
       if (chunkSize < MAX_MSGS_PER_TR && !round.stakes.empty()) {
            uint8 doubleChunkSize = 2 * chunkSize;
            this.completeRoundWithChunk{flag: 1, bounce: false}(
                roundId,
                doubleChunkSize < MAX_MSGS_PER_TR? doubleChunkSize : chunkSize
            );
            this.completeRoundWithChunk{flag: 1, bounce: false}(roundId, chunkSize);
        }
        setRound(roundId, round); } *)

Opaque DePoolContract_Ф__returnOrReinvest.

Lemma DePoolContract_Ф_completeRoundWithChunk_eval : forall ( Л_roundId : XInteger64 ) 
        ( Л_chunkSize : XInteger8 ) 
        (l: Ledger) , 
eval_state (  DePoolContract_Ф_completeRoundWithChunk Л_roundId Л_chunkSize ) l =        

(* : LedgerT (XErrorValue ( XValueValue True ) XInteger ) := *) 
(* require(msg.sender == address(this), Errors.IS_NOT_DEPOOL); *)
let req : bool :=  eval_state msg_sender l =?  eval_state tvm_address l in
(* tvm.accept(); *)
let la := exec_state (↓ tvm_accept) l in
(* if (!(isRound2(roundId) || m_poolClosed)) *)
let if1 : bool :=  negb ( ( eval_state ( ↓ RoundsBase_Ф_isRound2 Л_roundId ) l )   || 
                          ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l ) )%bool  in
(* optional(Round) optRound = fetchRound(roundId); *)
let optRound := eval_state ( RoundsBase_Ф_fetchRound Л_roundId ) l in
(* require(optRound.hasValue(), InternalErrors.ERROR519); *)
let req1 : bool := isSome optRound  in
(* round = optRound.get(); *)
let round := maybeGet optRound in
(* if (round.step != RoundStep.Completing) *)
let if2 : bool := negb ( eqb ( round ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_Completing ) in
(* round = _returnOrReinvest(round, chunkSize); *)
let optround' := eval_state ( ↓ DePoolContract_Ф__returnOrReinvest round Л_chunkSize ) la  in 


if req then 
   if if1 then Value ( Error I )
          else if req1 then 
                if if2 then Value ( Error I )  else match optround' with
                                                    | Value _ => Value (Value I)
                                                    | Error x => Error x
                                                    end   
                else Error (eval_state (↑ε8 InternalErrors_ι_ERROR519) l)
    else Error (eval_state (↑ε7 Errors_ι_IS_NOT_DEPOOL) l) .           
Proof. 
intros. destruct l. compute. repeat destructIf; auto.
match goal with 
| |- ?x  => match x with 
            | context [DePoolContract_Ф__returnOrReinvest ?a] => remember (DePoolContract_Ф__returnOrReinvest a)
            end
end.
destruct (l Л_chunkSize).

match goal with 
| |- ?x  => match x with 
            | context [p ?a] => remember (p a)
            end
end.

destruct p0.
destruct x; auto.

repeat destructIf; auto.

Qed. 


Ltac remDestructIf :=
  match goal with
    | |- ?x =>
      match x with
        | context [if ?b then _ else _] => case_eq b ; intros
        | _ => idtac
      end
  end.

Lemma DePoolContract_Ф_completeRoundWithChunk_exec : forall ( Л_roundId : XInteger64 ) 
                                                            ( Л_chunkSize : XInteger8 ) 
                                                            (l: Ledger) , 
exec_state (  DePoolContract_Ф_completeRoundWithChunk Л_roundId Л_chunkSize ) l =        

(* : LedgerT (XErrorValue ( XValueValue True ) XInteger ) := *) 
(* require(msg.sender == address(this), Errors.IS_NOT_DEPOOL); *)
let req : bool :=  eval_state msg_sender l =?  eval_state tvm_address l in
(* tvm.accept(); *)
let la := exec_state (↓ tvm_accept) l in
(* if (!(isRound2(roundId) || m_poolClosed)) *)
let if1 : bool :=  negb ( ( eval_state ( ↓ RoundsBase_Ф_isRound2 Л_roundId ) l )   || 
                          ( eval_state ( ↑12 ε DePoolContract_ι_m_poolClosed ) l ) )%bool  in
(* optional(Round) optRound = fetchRound(roundId); *)
let optRound := eval_state ( RoundsBase_Ф_fetchRound Л_roundId ) l in
(* require(optRound.hasValue(), InternalErrors.ERROR519); *)
let req1 : bool := isSome optRound  in
(* round = optRound.get(); *)
let round := maybeGet optRound in
(* if (round.step != RoundStep.Completing) *)
let if2 : bool := negb ( eqb ( round ->> RoundsBase_ι_Round_ι_step ) RoundsBase_ι_RoundStepP_ι_Completing ) in
(* round = _returnOrReinvest(round, chunkSize); *)
let (round', l__returnOrReinvest) := run ( ↓ DePoolContract_Ф__returnOrReinvest round Л_chunkSize ) la  in 
(* let round'' := errorMapDefault Datatypes.id round' default in *)
let oldMessages := VMState_ι_messages ( Ledger_ι_VMState l__returnOrReinvest ) in
let newMessage1  := {|  contractAddress :=  0 ;
                        contractFunction := DePoolContract_Ф_completeRoundWithChunkF Л_roundId
                          ( if ( (2 * Л_chunkSize) <? (eval_state (↑12 ε DePoolContract_ι_MAX_MSGS_PER_TR) l__returnOrReinvest) )
                            then (2 * Л_chunkSize)
                            else Л_chunkSize ) ;
                            contractMessage := {| messageValue := default ;
                                                  messageFlag  := 1 ; 
                                                  messageBounce := false
                                                  |} |} in
let newMessage2  := {| contractAddress :=  0 ;
                       contractFunction := DePoolContract_Ф_completeRoundWithChunkF Л_roundId Л_chunkSize  ;
                       contractMessage := {| messageValue := default ;
                                             messageFlag  := 1 ; 
                                             messageBounce := false
                                                  |} |} in
let l' :=  {$ l__returnOrReinvest With ( VMState_ι_messages , newMessage2 :: newMessage1 :: oldMessages ) $}  in                                               

if req then 
   if if1 then la
          else if req1 then 
                if if2 then la else match round' with
                                   | Value round'' =>         (* if (chunkSize < MAX_MSGS_PER_TR && !round.stakes.empty()) { *)
                                   let if3 : bool := ( ( Л_chunkSize <? ( eval_state (↑12 ε DePoolContract_ι_MAX_MSGS_PER_TR ) l__returnOrReinvest ) ) && 
                                                       ( negb ( xHMapIsNull (round'' ->> RoundsBase_ι_Round_ι_stakes) ) ) )%bool in

                                   if if3 then exec_state ( ↓ RoundsBase_Ф_setRound Л_roundId round'' ) l'
                                          else exec_state ( ↓ RoundsBase_Ф_setRound Л_roundId round'' ) l__returnOrReinvest                    
                                   | Error x => l__returnOrReinvest
                                   end   
                else la
    else l .
Proof.
        intros. destruct l. compute. repeat remDestructIf; auto.
        match goal with 
        | |- ?x  => match x with 
                    | context [DePoolContract_Ф__returnOrReinvest ?a] => remember (DePoolContract_Ф__returnOrReinvest a)
                    end
        end.
        destruct (l Л_chunkSize).
        
        match goal with 
        | |- ?x  => match x with 
                    | context [p ?a] => remember (p a)
                    end
        end.
        
        destruct p0.
        destruct x; auto.

        match goal with 
        | |- ?x  => match x with 
                    | context [DePoolContract_Ф__returnOrReinvest ?a] => remember (DePoolContract_Ф__returnOrReinvest a)
                    end
        end.
        destruct (l Л_chunkSize).
        
        match goal with 
        | |- ?x  => match x with 
                    | context [p ?a] => remember (p a)
                    end
        end.
        
        destruct p0.
        destruct x; auto.

        match goal with 
        | |- ?x  => match x with 
                    | context [DePoolContract_Ф__returnOrReinvest ?a] => remember (DePoolContract_Ф__returnOrReinvest a)
                    end
        end.
        destruct (l Л_chunkSize).
        
        match goal with 
        | |- ?x  => match x with 
                    | context [p ?a] => remember (p a)
                    end
        end.
        
        destruct p0.
        destruct x; auto.

        repeat remDestructIf; auto.

        match goal with 
        | |- ?x  => match x with 
                    | context [DePoolContract_Ф__returnOrReinvest ?a] => remember (DePoolContract_Ф__returnOrReinvest a)
                    end
        end.
        destruct (l Л_chunkSize).
        
        match goal with 
        | |- ?x  => match x with 
                    | context [p ?a] => remember (p a)
                    end
        end.
        
        destruct p0.
        destruct x; auto.

        match goal with 
        | |- ?x  => match x with 
                    | context [DePoolContract_Ф__returnOrReinvest ?a] => remember (DePoolContract_Ф__returnOrReinvest a)
                    end
        end.
        destruct (l Л_chunkSize).
        
        match goal with 
        | |- ?x  => match x with 
                    | context [p ?a] => remember (p a)
                    end
        end.
        
        destruct p0.
        destruct x; auto.
Qed.        
