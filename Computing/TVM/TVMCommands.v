Require Export Coq.Program.Basics.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Program.Combinators.
Require Export ZArith.
Require Export Lists.List.
Require Export Ascii.
Require Export Strings.String. 
Require Export CommonHelpers.
Require Export StringHelpers.

Require Export FinProof.ProgrammingWith.

Local Open Scope record.
Local Open Scope program_scope.

Require Export FinProof.Common.
Require Export FinProof.StateMonad6.
Require Export FinProof.StateMonad6Instances.

Require Export TVMModel.Base.Definitions.State.
Require Export TVMModel.Base.Definitions.TVMBitString.
Require Export TVMModel.Base.Definitions.TVMBit.
Export TVMBitStringNotations.
Require Export TVMModel.Base.Definitions.StateTransforms.
Require Export TVMModel.Base.Definitions.TVMCellHashmap.
Require Export TVMModel.Base.Definitions.OpResultMonad.

Require Export TVMModel.Operations.Definitions.CTOS.
Require Export TVMModel.Operations.Definitions.PUSHINT.
Require Export TVMModel.Operations.Definitions.ADD.
Require Export TVMModel.Operations.Definitions.LEQ.
Require Export TVMModel.Base.Definitions.State.
Require Export TVMModel.Base.Definitions.TVMCell.
Require Export TVMModel.Base.Definitions.TVMIntN.
Require Export TVMModel.Base.Definitions.TVMBitString.
Require Export TVMModel.Base.Proofs.Basic.
Require Export TVMModel.Operations.Definitions.ENDC.
Require Export TVMModel.Operations.Definitions.NEWC.
Require Export TVMModel.Operations.Definitions.STONES.
Require Export TVMModel.Operations.Definitions.PUSH.
Require Export TVMModel.Operations.Definitions.SECOND.
Require Export TVMModel.Operations.Definitions.PUSHINT.
Require Export TVMModel.Operations.Definitions.NEWC.
Require Export TVMModel.Operations.Definitions.ROT.
Require Export TVMModel.Operations.Definitions.DICTUSETB.
Require Export TVMModel.Operations.Definitions.POP.
Require Export TVMModel.Operations.Definitions.PUSHCTR7.
Require Export TVMModel.Operations.Definitions.SETSECOND.
Require Export TVMModel.Operations.Definitions.STU.
Require Export TVMModel.Operations.Definitions.POPCTR7.
Require Export TVMModel.Base.Definitions.TVMSlice.
Require Export TVMModel.Base.Definitions.Exception.
Require Export TVMModel.Base.Definitions.Hex.
Require Export TVMModel.Operations.Definitions.PUSH.
Require Export TVMModel.Operations.Definitions.SECOND.
Require Export TVMModel.Operations.Definitions.PUSHINT.
Require Export TVMModel.Operations.Definitions.NEWC.
Require Export TVMModel.Operations.Definitions.ROT.
Require Export TVMModel.Operations.Definitions.DICTUSETB.
Require Export TVMModel.Operations.Definitions.POP.
Require Export TVMModel.Operations.Definitions.PUSHCTR7.
Require Export TVMModel.Operations.Definitions.SETSECOND.
Require Export TVMModel.Operations.Definitions.STU.
(* 06-02-2020 *)
Require Export TVMModel.Operations.Definitions.ACCEPT.
Require Export TVMModel.Operations.Definitions.ADD.
Require Export TVMModel.Operations.Definitions.AND.
Require Export TVMModel.Operations.Definitions.BBITS.
Require Export TVMModel.Operations.Definitions.DEC.
Require Export TVMModel.Operations.Definitions.DICTUDEL.
Require Export TVMModel.Operations.Definitions.DICTUGET.
Require Export TVMModel.Operations.Definitions.DICTUMAX.
Require Export TVMModel.Operations.Definitions.DIV.
Require Export TVMModel.Operations.Definitions.ENDS.
Require Export TVMModel.Operations.Definitions.EQINT.
Require Export TVMModel.Operations.Definitions.EQUAL.
Require Export TVMModel.Operations.Definitions.EXECUTE.
Require Export TVMModel.Operations.Definitions.FIRST.
Require Export TVMModel.Operations.Definitions.GEQ.
Require Export TVMModel.Operations.Definitions.GREATER.
Require Export TVMModel.Operations.Definitions.IFJMP.
Require Export TVMModel.Operations.Definitions.IFNOT.
Require Export TVMModel.Operations.Definitions.IFNOTJMP.
Require Export TVMModel.Operations.Definitions.IFOP.
Require Export TVMModel.Operations.Definitions.INC.
Require Export TVMModel.Operations.Definitions.ISNULL.
Require Export TVMModel.Operations.Definitions.JMP.
Require Export TVMModel.Operations.Definitions.LDDICT.
Require Export TVMModel.Operations.Definitions.LDI.
Require Export TVMModel.Operations.Definitions.LDIX.
Require Export TVMModel.Operations.Definitions.LDREF.
Require Export TVMModel.Operations.Definitions.LDSLICEX.
Require Export TVMModel.Operations.Definitions.LDU.
Require Export TVMModel.Operations.Definitions.LDUX.
Require Export TVMModel.Operations.Definitions.LEQ.
Require Export TVMModel.Operations.Definitions.LESS.
Require Export TVMModel.Operations.Definitions.MUL.
Require Export TVMModel.Operations.Definitions.NEQ.
Require Export TVMModel.Operations.Definitions.NOP.
Require Export TVMModel.Operations.Definitions.NOT.
Require Export TVMModel.Operations.Definitions.NULL.
Require Export TVMModel.Operations.Definitions.OR.
Require Export TVMModel.Operations.Definitions.POP.
Require Export TVMModel.Operations.Definitions.POPROOT.
Require Export TVMModel.Operations.Definitions.PRINTSTR.
Require Export TVMModel.Operations.Definitions.PUSHROOT.
Require Export TVMModel.Operations.Definitions.SCHKBITSQ.
Require Export TVMModel.Operations.Definitions.SDEMPTY.
Require Export TVMModel.Operations.Definitions.SDEQ.
Require Export TVMModel.Operations.Definitions.SEMPTY.
Require Export TVMModel.Operations.Definitions.SETCP.
Require Export TVMModel.Operations.Definitions.SETTHIRD.
Require Export TVMModel.Operations.Definitions.SREMPTY.
Require Export TVMModel.Operations.Definitions.STBR.
Require Export TVMModel.Operations.Definitions.STDICT.
Require Export TVMModel.Operations.Definitions.STGRAMS.
Require Export TVMModel.Operations.Definitions.STI.
Require Export TVMModel.Operations.Definitions.STREF.
Require Export TVMModel.Operations.Definitions.STREFR.
Require Export TVMModel.Operations.Definitions.STSLICE.
Require Export TVMModel.Operations.Definitions.STZEROES.
Require Export TVMModel.Operations.Definitions.SUB.
Require Export TVMModel.Operations.Definitions.THIRD.
Require Export TVMModel.Operations.Definitions.THROWANY.
Require Export TVMModel.Operations.Definitions.THROWIF.
Require Export TVMModel.Operations.Definitions.THROWIFNOT.
Require Export TVMModel.Operations.Definitions.TPUSH.
Require Export TVMModel.Operations.Definitions.TUPLE.
Require Export TVMModel.Operations.Definitions.UFITS.
Require Export TVMModel.Operations.Definitions.XCHG.
(********** 12/02/2020  ***************************)
Require Export TVMModel.Operations.Definitions.BLKDROP.
Require Export TVMModel.Operations.Definitions.BLKSWAP.
Require Export TVMModel.Operations.Definitions.DICTUGETNEXT.
Require Export TVMModel.Operations.Definitions.DICTUGETREF.
Require Export TVMModel.Operations.Definitions.DICTUMINREF.
Require Export TVMModel.Operations.Definitions.DICTUSETREF.
Require Export TVMModel.Operations.Definitions.DROP2.
Require Export TVMModel.Operations.Definitions.GETPARAM.
Require Export TVMModel.Operations.Definitions.GTINT.
Require Export TVMModel.Operations.Definitions.IFELSE.
Require Export TVMModel.Operations.Definitions.INDEX.
Require Export TVMModel.Operations.Definitions.LDDICTS.
Require Export TVMModel.Operations.Definitions.LDREFRTOS.
Require Export TVMModel.Operations.Definitions.LDSLICE.
Require Export TVMModel.Operations.Definitions.LSHIFT.
Require Export TVMModel.Operations.Definitions.NEQINT.
Require Export TVMModel.Operations.Definitions.NEWDICT.
Require Export TVMModel.Operations.Definitions.ONLYTOPX.
Require Export TVMModel.Operations.Definitions.PLDDICT.
Require Export TVMModel.Operations.Definitions.PLDI.
Require Export TVMModel.Operations.Definitions.PLDREF.
Require Export TVMModel.Operations.Definitions.PLDREFIDX.
Require Export TVMModel.Operations.Definitions.PLDU.
Require Export TVMModel.Operations.Definitions.POP.
Require Export TVMModel.Operations.Definitions.PUSH2.
Require Export TVMModel.Operations.Definitions.PUSHPOW2DEC. 
Require Export TVMModel.Operations.Definitions.PUSHSLICE.
Require Export TVMModel.Operations.Definitions.RET.
Require Export TVMModel.Operations.Definitions.ROTREV.
Require Export TVMModel.Operations.Definitions.RSHIFT.
Require Export TVMModel.Operations.Definitions.SDSKIPFIRST.
Require Export TVMModel.Operations.Definitions.SKIPDICT.
Require Export TVMModel.Operations.Definitions.SPLIT.
Require Export TVMModel.Operations.Definitions.SSKIPFIRST.
Require Export TVMModel.Operations.Definitions.STBREF.
Require Export TVMModel.Operations.Definitions.STBREFR.
Require Export TVMModel.Operations.Definitions.STIR.
Require Export TVMModel.Operations.Definitions.STSLICER.
Require Export TVMModel.Operations.Definitions.STUR.
Require Export TVMModel.Operations.Definitions.UNTIL.
Require Export TVMModel.Operations.Definitions.BLESS.
Require Export TVMModel.Operations.Definitions.BREMBITS.
Require Export TVMModel.Operations.Definitions.CONDSEL.
Require Export TVMModel.Operations.Definitions.DROPX.
Require Export TVMModel.Operations.Definitions.PUSHCONT.
Require Export TVMModel.Operations.Definitions.PUSHPOW2DEC.
Require Export TVMModel.Operations.Definitions.PUSHPOW2DEC.
Require Export TVMModel.Operations.Definitions.SBITS.
Require Export TVMModel.Operations.Definitions.SETINDEX.
Require Export TVMModel.Operations.Definitions.SREFS.
Require Export TVMModel.Operations.Definitions.SUBR.
Require Export TVMModel.Operations.Definitions.UNPAIR.
Require Export TVMModel.Operations.Definitions.DICTUMIN.
Require Export TVMModel.Operations.Definitions.HASHCU.
Require Export TVMModel.Operations.Definitions.REVERSE.
Require Export TVMModel.Operations.Definitions.SCUTFIRST.
(****************)
Require Export TVMModel.Operations.Definitions.CALL.
Require Export TVMModel.Operations.Definitions.CHKSIGNU.
Require Export TVMModel.Operations.Definitions.LDMSGADDR.

Require Export TVMModel.Operations.Definitions.PARSEMSGADDR.
Require Export TVMModel.Operations.Definitions.PUSHREFCONT.
Require Export TVMModel.Operations.Definitions.SENDRAWMSG.
Require Export TVMModel.Operations.Definitions.SETCODE.
Require Export TVMModel.Operations.Definitions.LESSINT.

Require Export TVMModel.Operations.Definitions.DEPTH.
Require Export TVMModel.Operations.Definitions.PICK.

Require Export TVMModel.Base.Definitions.TVMSlice.
Require Export TVMModel.Base.Definitions.Basic.

Notation "·0"  := (Here)       (at level 60, right associativity). 
Notation "·1"  := (Next (·0))  (at level 60, right associativity).
Notation "·2"  := (Next (·1))  (at level 60, right associativity).
Notation "·3"  := (Next (·2))  (at level 60, right associativity). 
Notation "·4"  := (Next (·3))  (at level 60, right associativity).
Notation "·5"  := (Next (·4))  (at level 60, right associativity).
Notation "·6"  := (Next (·5))  (at level 60, right associativity).
Notation "·7"  := (Next (·6))  (at level 60, right associativity).

Bind Scope struct_scope with TVMState.
 
Global Instance Struct_TVMContinuation : Struct TVMContinuation := {
  fields := [@existT _ _ _ contSlice,
             @existT _ _ _ contStack,
             @existT _ _ _ contRegistries,
             @existT _ _ _ contCodePage,
             @existT _ _ _ contUnknown] ;
  ctor   := _TVMContinuationInit
}.

Global Instance Acc_TVMState_contSlice : Accessor contSlice := { acc := ·0 }.
Global Instance Acc_TVMState_contStack : Accessor contStack       := { acc := ·1 }.
Global Instance Acc_TVMState_contRegistries : Accessor contRegistries  := { acc := ·2 }.
Global Instance Acc_TVMState_contCodePage : Accessor contCodePage := { acc := ·3 }.
Global Instance Acc_TVMState_contUnknown : Accessor contUnknown       := { acc := ·4 }.

(* Compute {$ (ec_quit 0)  with contUnknown := 5 $}. *)

Bind Scope struct_scope with TVMRegistry.
 
Global Instance Struct_TVMCRegistry : Struct TVMRegistry := {
  fields := [@existT _ _ _ regC0,
             @existT _ _ _ regC1,
             @existT _ _ _ regC2,
             @existT _ _ _ regC3,
             @existT _ _ _ regC4,
             @existT _ _ _ regC5,
             @existT _ _ _ regC7] ;
  ctor   := _TVMRegistryInit
}.

Global Instance Acc_TVMRegistry_regC0 : Accessor regC0 := { acc := ·0 }.
Global Instance Acc_TVMRegistry_regC1 : Accessor regC1 := { acc := ·1 }.
Global Instance Acc_TVMRegistry_regC2 : Accessor regC2 := { acc := ·2 }.
Global Instance Acc_TVMRegistry_regC3 : Accessor regC3 := { acc := ·3 }.
Global Instance Acc_TVMRegistry_regC4 : Accessor regC4 := { acc := ·4 }.
Global Instance Acc_TVMRegistry_regC5 : Accessor regC5 := { acc := ·5 }.
Global Instance Acc_TVMRegistry_regC7 : Accessor regC7 := { acc := ·6 }.

Global Instance Struct_TVMState : Struct TVMState := {
  fields := [@existT _ _ _ tvmRegistry, 
             @existT _ _ _ tvmCC, 
             @existT _ _ _ tvmGas,
             @existT _ _ _ tvmWorld] ;
  ctor   := (* Build *)_TVMState
}.

Global Instance Acc_TVMState_tvmRegistry : Accessor tvmRegistry := { acc := ·0 }.
Global Instance Acc_TVMState_tvmCC       : Accessor tvmCC       := { acc := ·1 }.
Global Instance Acc_TVMState_tvmGas      : Accessor tvmGas      := { acc := ·2 }.


(*embeddedType for TVMRegistry *)
Definition projEmbed_TVMRegistry : TVMState -> TVMRegistry := tvmRegistry.
Definition injEmbed_TVMRegistry (r: TVMRegistry) (s: TVMState): TVMState :=
{$ s with tvmRegistry := r $}.

(*embeddedType for TVMContinuation *)
Definition projEmbed_TVMContinuation: TVMState -> TVMContinuation := tvmCC.
Definition injEmbed_TVMContinuation (c: TVMContinuation) (s: TVMState): TVMState :=
{$ s with tvmCC := c $}.

Lemma projinj_TVMContinuation: forall (c : TVMContinuation) (s : TVMState), 
      projEmbed_TVMContinuation (injEmbed_TVMContinuation c s) = c.
Proof.
 intros. compute. auto.
Qed.

Lemma injproj_TVMContinuation : forall (s : TVMState), 
      injEmbed_TVMContinuation (projEmbed_TVMContinuation s) s = s.
Proof.
 intros. destruct s. compute. auto.
Qed.

Lemma projinj_TVMRegistry: forall (r: TVMRegistry) (s : TVMState), 
      projEmbed_TVMRegistry (injEmbed_TVMRegistry r s) = r.
Proof.
 intros. compute. auto.
Qed.

Lemma injproj_TVMRegistry : forall (s : TVMState), 
      injEmbed_TVMRegistry (projEmbed_TVMRegistry s) s = s.
Proof.
 intros. destruct s. compute. auto.
Qed.

Lemma injinj_TVMRegistry : forall (r1 r2 : TVMRegistry) (s : TVMState), 
      injEmbed_TVMRegistry r1 (injEmbed_TVMRegistry r2 s) =
      injEmbed_TVMRegistry r1 s.
Proof.
 intros. destruct s. compute. auto.
Qed.


Instance embeddedTVMRegistry: EmbeddedType TVMState TVMRegistry :=
{
 projEmbed := projEmbed_TVMRegistry;
 injEmbed := injEmbed_TVMRegistry;
 projinj := projinj_TVMRegistry;
 injproj := injproj_TVMRegistry;
 injinj  := injinj_TVMRegistry
}.

Lemma injinj_TVMContinuation : forall (c1 c2 : TVMContinuation) (s : TVMState), 
      injEmbed_TVMContinuation c1 (injEmbed_TVMContinuation c2 s) =
      injEmbed_TVMContinuation c1 s.
Proof.
 intros. destruct s. compute. auto.
Qed.

Instance embeddedTVMContinuation: EmbeddedType TVMState TVMContinuation :=
{
 projEmbed := projEmbed_TVMContinuation;
 injEmbed := injEmbed_TVMContinuation;
 projinj := projinj_TVMContinuation;
 injproj := injproj_TVMContinuation;
 injinj := injinj_TVMContinuation
}.


(*embeddedType for TVMGasLimit *)
Definition projEmbed_TVMGasLimit : TVMState -> TVMGasLimit := tvmGas.
Definition injEmbed_TVMGasLimit (g: TVMGasLimit) (s: TVMState): TVMState :=
{$ s with tvmGas := g $}.

Lemma projinj_TVMGasLimit: forall (g : TVMGasLimit) (s : TVMState), 
      projEmbed_TVMGasLimit (injEmbed_TVMGasLimit g s) = g.
Proof.
 intros. compute. auto.
Qed.

Lemma injproj_TVMGasLimit : forall (s : TVMState), 
      injEmbed_TVMGasLimit (projEmbed_TVMGasLimit s) s = s.
Proof.
 intros. destruct s. compute. auto.
Qed.

Lemma injinj_TVMGasLimit: forall (g1 g2 : TVMGasLimit) (s : TVMState), 
      injEmbed_TVMGasLimit g1 (injEmbed_TVMGasLimit g2 s) =
      injEmbed_TVMGasLimit g1 s.
Proof.
 intros. destruct s. compute. auto.
Qed.

Instance embeddedTVMGasLimit: EmbeddedType TVMState TVMGasLimit :=
{
 projEmbed := projEmbed_TVMGasLimit;
 injEmbed := injEmbed_TVMGasLimit;
 projinj := projinj_TVMGasLimit;
 injproj := injproj_TVMGasLimit;
 injinj := injinj_TVMGasLimit
}.

Definition StateT := simpleStateM.

Definition monadTVMStateStateT : MonadStateT (M:=OpResultContainer) TVMState 
                                StateT := 
           simpleStateMMonadStateT TVMState (M:=OpResultContainer).
Existing Instance monadTVMStateStateT.

Definition monadTVMContStateT : MonadStateT (M:=OpResultContainer) TVMContinuation 
                                StateT := 
           simpleStateMMonadStateT TVMContinuation (M:=OpResultContainer).
Existing Instance monadTVMContStateT.

Definition TVMStateT := StateT TVMState OpResultContainer.
Definition TVMRegistryT := StateT TVMRegistry OpResultContainer.
Definition TVMContinuationT := StateT TVMContinuation OpResultContainer.
Definition TVMGasLimitT := StateT TVMGasLimit OpResultContainer.

Create HintDb tvm_monadstate_db.
Hint Transparent TVMStateT: tvm_monadstate_db.

(********************move somewhere***************************)

Arguments _OpResultContainerNormal [T].
Arguments _OpResultContainerException [T].
Require Export  TVMModel.Base.Definitions.Exception.

Definition contStackM (c: TVMContinuation) : OpResultContainer TVMStack :=
match c with
| _TVMContinuationInit _ s _ _ _ => _OpResultContainerNormal s
| ec_quit e => _OpResultContainerException (FATAL_EXCEPTION 0)
| ec_until _ _ _ => _OpResultContainerException (FATAL_EXCEPTION 0)
end.

Definition stackFunctionContEmbed (f: TVMStack -> OpResultContainer TVMStack)
                                  (c: TVMContinuation): OpResultContainer TVMContinuation :=
contStackM c >>= 
f  >>= 
(fun stck => return! {$ c with contStack := stck $}).

Existing Instance simpleStateMMonadTrans.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.
Local Open Scope monad_scope.

Notation "'do' a ← e ; c" := (e >>= fun a => c) (at level 60, right associativity): monad_scope.
Notation "↑ m" := (liftEmbeddedState m) (at level 11, right associativity): monad_scope.
Notation "'ε' e" := (embed_fun e) (at level 60, right associativity): monad_scope.
Notation "'returnε' e" := (do ee ← ε e; return! ee)%monad (at level 60, right associativity): monad_scope.
Notation "'↑returnε' e" := (do ee ← ↑ (ε e); return! ee)%monad (at level 60, right associativity): monad_scope.
Notation "'bindε' e 'to' a 'in' f" := (do a ← ε e; f)%monad (at level 60, right associativity): monad_scope.
Notation "'↑bindε' e 'to' a 'in' f" := (do a ← ↑(ε e); f)%monad (at level 60, right associativity): monad_scope.
Notation "x ; void!" := (bind_  x (return! I)) (at level 60, right associativity): monad_scope.

Definition stackFunctionStateEmbed (f: TVMStack -> OpResultContainer TVMStack)
                                    : TVMContinuationT True:=
do c ← get (T:=StateT);
do newc ← lift (stackFunctionContEmbed f c);
   put newc;
   void!.


Arguments _OpResultContainerNormal [T].

Inductive IsContinuation : TVMContinuation -> Prop :=
| is_cont_init : forall sl st r cp u, IsContinuation (_TVMContinuationInit sl st r cp u).

Lemma TVMContinuation_eq: forall c c',
IsContinuation c -> IsContinuation c' -> 
contSlice c = contSlice c' ->
contStack c = contStack c' ->
contRegistries c = contRegistries c' ->
contCodePage c = contCodePage c' ->
contUnknown c = contUnknown c' ->
c = c'.
Proof.
 intros. destruct c. destruct c'.
 simpl in *. subst. auto.
 inversion H0. inversion H.
 inversion H0. inversion H. inversion H.
Qed.

Definition Exec_ACCEPT : TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_ACCEPT TVMBitStringEmpty tvmSliceEmpty st);
   put st'; void!.

Definition Exec_ADD : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_ADD TVMBitStringEmpty).

Definition Exec_AND : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_AND TVMBitStringEmpty).

Definition Exec_BBITS : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_BBITS TVMBitStringEmpty).

Definition Exec_BLESS : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_BLESS TVMBitStringEmpty).

Definition Exec_BREMBITS : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_BREMBITS TVMBitStringEmpty).

Definition Exec_CONDSEL : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_CONDSEL TVMBitStringEmpty).

Definition Exec_BLKDROP (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_BLKDROP i).

Definition Exec_BLKSWAP (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_BLKSWAP i).

Definition Exec_CTOS : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_CTOS TVMBitStringEmpty).

Definition Exec_CTOS' : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_CTOS TVMBitStringEmpty).

Definition Exec_DEC : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DEC TVMBitStringEmpty).

Definition Exec_DICTUDEL : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DICTUDEL TVMBitStringEmpty).

Definition Exec_DICTUGETNEXT : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DICTUGETNEXT TVMBitStringEmpty).

Definition Exec_DICTUGETREF : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DICTUGETREF TVMBitStringEmpty).

Definition Exec_DICTUGETREF' : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DICTUGETREF' TVMBitStringEmpty).

Definition Exec_DICTUMINREF : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DICTUMINREF TVMBitStringEmpty).

Definition Exec_DICTUSETREF : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DICTUSETREF TVMBitStringEmpty).

Definition Exec_DICTUSETREF' : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DICTUSETREF' TVMBitStringEmpty).

Definition Exec_DICTUGET : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DICTUGET TVMBitStringEmpty).

Definition Exec_DICTUGET' : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DICTUGET' TVMBitStringEmpty).

Definition Exec_DICTUMAX : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DICTUMAX TVMBitStringEmpty).

Definition Exec_DICTUSETB: TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DICTUSETB TVMBitStringEmpty).

Definition Exec_DIV : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DIV TVMBitStringEmpty).

(* Check  exec_DROP. *)

Definition Exec_DROP : TVMStateT True :=
↑ stackFunctionStateEmbed exec_DROP .

Definition Exec_DROP2 : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DROP2 TVMBitStringEmpty).

Definition Exec_DROPX : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DROPX TVMBitStringEmpty).

Definition Exec_ENDC : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_ENDC TVMBitStringEmpty).

Definition Exec_ENDS : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_ENDS TVMBitStringEmpty).

Definition Exec_EQINT (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_EQINT i).

Definition Exec_EQUAL : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_EQUAL TVMBitStringEmpty).

Definition Exec_EXECUTE (i : TVMBitString) : TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_EXECUTE i tvmSliceEmpty st);
   put st'; void!.

Definition Exec_FIRST : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_FIRST TVMBitStringEmpty).

Definition Exec_GEQ : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_GEQ TVMBitStringEmpty).

Definition Exec_GETPARAM (i : TVMBitString) : TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_GETPARAM i tvmSliceEmpty st);
   put st'; void!.

Definition Exec_GTINT (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_GTINT i).

Definition Exec_IFELSE (i : TVMBitString) : TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_IFELSE i tvmSliceEmpty st);
   put st'; void!.

Definition Exec_GREATER : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_GREATER TVMBitStringEmpty).

Definition Exec_IFJMP (* (i : TVMBitString) *) : TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_IFJMP TVMBitStringEmpty tvmSliceEmpty st);
   put st'; void!.

Definition Exec_IFNOT (* (i : TVMBitString) *): TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_IFNOT TVMBitStringEmpty tvmSliceEmpty st);
   put st'; void!.

Definition Exec_IFNOTJMP (i : TVMBitString): TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_IFNOTJMP i tvmSliceEmpty st);
   put st'; void!.

Definition Exec_IFOP (i : TVMBitString): TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_IFOP i tvmSliceEmpty st);
   put st'; void!.

Definition Exec_INC : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_INC TVMBitStringEmpty).

Definition Exec_INDEX (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_INDEX i).

Definition Exec_ISNULL : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_ISNULL TVMBitStringEmpty).

Definition Exec_JMP (z : Z): TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_JMP (Z2IBS 8 z) tvmSliceEmpty st);
   put st'; void!.

Definition Exec_LDDICTS : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LDDICTS TVMBitStringEmpty).

Definition Exec_LDDICT : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LDDICT TVMBitStringEmpty).

Definition Exec_LDI (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LDI i).

Definition Exec_LDI' (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LDI' i).

Definition Exec_LDIX : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LDIX TVMBitStringEmpty).

Definition Exec_LDREF : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LDREF TVMBitStringEmpty).

Definition Exec_LDREFRTOS : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LDREFRTOS TVMBitStringEmpty).

Definition Exec_LDSLICE (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LDSLICE i).

Definition Exec_LDSLICEX : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LDSLICEX TVMBitStringEmpty).

Definition Exec_LDU (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LDU i).

Definition Exec_LDU' (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LDU' i).

Definition Exec_LDUX : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LDUX TVMBitStringEmpty).

Definition Exec_LESS : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LESS TVMBitStringEmpty).

Definition Exec_LSHIFT : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LSHIFT_stack TVMBitStringEmpty).

Definition Exec_RSHIFT : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_RSHIFT_stack TVMBitStringEmpty).

Definition Exec_MUL : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_MUL TVMBitStringEmpty).

Definition Exec_NEQ : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NEQ TVMBitStringEmpty).

Definition Exec_NEQINT (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NEQINT i).

Definition Exec_NEWC: TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NEWC TVMBitStringEmpty).

Definition Exec_NEWDICT: TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NEWDICT TVMBitStringEmpty).

Definition Exec_PUSHCONTF80 (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PUSHCONT8F0 i).

Definition Exec_PUSHPOW2DEC (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PUSHPOW2DEC i).

Definition Exec_PUSHSLICED0 (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PUSHSLICED0 i).

Definition Exec_PUSHNULL: TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PUSHNULL TVMBitStringEmpty).

Definition Exec_NOP : TVMStateT True :=
↑ stackFunctionStateEmbed  ( exec_NOP ).

Definition Exec_NOT : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NOT TVMBitStringEmpty).

Definition Exec_NULL : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NULL TVMBitStringEmpty).

Definition Exec_ONLYTOPX : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_ONLYTOPX TVMBitStringEmpty).

Definition Exec_OR : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_OR TVMBitStringEmpty).

Definition Exec_PLDDICT : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PLDDICT TVMBitStringEmpty).

Definition Exec_PLDI (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PLDI i).

Definition Exec_PLDI' (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PLDI' i).

Definition Exec_PLDREF : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PLDREF TVMBitStringEmpty).

Definition Exec_PLDREFIDX (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PLDREFIDX i).

Definition Exec_PLDU (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PLDU i).

Definition Exec_PLDU' (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PLDU' i).

Definition Exec_LESSINT (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LESSINT i).

Definition Exec_POP (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_POP i).

Definition Exec_POPCTR7: TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_POPCTR7 TVMBitStringEmpty tvmSliceEmpty st);
   put st'; void!.

Definition Exec_POPROOT : TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_POPROOT TVMBitStringEmpty tvmSliceEmpty st);
   put st'; void!.

Definition Exec_PRINTSTR : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PRINTSTR TVMBitStringEmpty).

Definition Exec_PUSH (i: TVMBitString): TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PUSH i).

Definition Exec_PUSH2 (i: TVMBitString): TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PUSH2 i).

Definition Exec_PUSHCTR7 : TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_PUSHCTR7 TVMBitStringEmpty tvmSliceEmpty st);
   put st'; void!.

Definition Exec_PUSHINT80 (i: TVMBitString): TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PUSHINT80 i).

Definition Exec_PUSHINT81 (i: TVMBitString): TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PUSHINT81 i).

Definition Exec_PUSHINT82 (s: TVMBitString): TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PUSHINT82 s).

Definition Exec_LEQ : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LEQ TVMBitStringEmpty).

Definition Exec_PUSHINT7 (i: TVMBitString): TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PUSHINT7 i ).

Definition Exec_PUSHROOT : TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_PUSHROOT TVMBitStringEmpty tvmSliceEmpty st);
   put st'; void!.

Definition Exec_RET : TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_RET TVMBitStringEmpty tvmSliceEmpty st);
   put st'; void!.

Definition Exec_ROT: TVMStateT True :=
↑ stackFunctionStateEmbed (exec_ROT TVMBitStringEmpty).

Definition Exec_ROTREV: TVMStateT True :=
↑ stackFunctionStateEmbed (exec_ROTREV TVMBitStringEmpty).

Definition Exec_SBITS : TVMStateT True :=
↑ stackFunctionStateEmbed ( exec_SBITS TVMBitStringEmpty).

Definition Exec_SCHKBITSQ : TVMStateT True :=
↑ stackFunctionStateEmbed ( exec_SCHKBITSQ ).

Definition Exec_SDEMPTY : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SDEMPTY TVMBitStringEmpty).

Definition Exec_SDEQ : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SDEQ TVMBitStringEmpty).

Definition Exec_SDSKIPFIRST : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SDSKIPFIRST TVMBitStringEmpty).

Definition Exec_SDSKIPFIRST' : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SDSKIPFIRST' TVMBitStringEmpty).


Definition Exec_SECOND : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SECOND TVMBitStringEmpty).

Definition Exec_SEMPTY : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SEMPTY TVMBitStringEmpty).

Definition Exec_SETCP (i: TVMBitString): TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_SETCP i tvmSliceEmpty st);
   put st'; void!.

Definition Exec_SETINDEX (i: TVMBitString): TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SETINDEX i ).

Definition Exec_SETSECOND : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SETSECOND TVMBitStringEmpty).

Definition Exec_SETTHIRD : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SETTHIRD TVMBitStringEmpty).

Definition Exec_SKIPDICT : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SKIPDICT TVMBitStringEmpty ).

Definition Exec_SPLIT : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SPLIT TVMBitStringEmpty).

Definition Exec_SREFS : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SREFS TVMBitStringEmpty).

Definition Exec_SREMPTY : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SREMPTY TVMBitStringEmpty).

Definition Exec_SSKIPFIRST : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SSKIPFIRST TVMBitStringEmpty).

Definition Exec_SSKIPFIRST' : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SSKIPFIRST' TVMBitStringEmpty).

Definition Exec_STBR : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STBR TVMBitStringEmpty).

Definition Exec_STBREF : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STBREF TVMBitStringEmpty ).

Definition Exec_STBREFR : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STBREFR TVMBitStringEmpty ).

Definition Exec_STDICT : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STDICT TVMBitStringEmpty).

Definition Exec_STGRAMS : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STGRAMS TVMBitStringEmpty).

Definition Exec_STI (i: TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STI i).

Definition Exec_STI' (i: TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STI' i).

Definition Exec_STIR (i: TVMBitString): TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STIR i).

Definition Exec_STIR' (i: TVMBitString): TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STIR' i).

Definition Exec_STONES : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STONES TVMBitStringEmpty).

Definition Exec_STREF : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STREF TVMBitStringEmpty).

Definition Exec_STREFR : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STREFR TVMBitStringEmpty).

Definition Exec_STSLICE : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STSLICE TVMBitStringEmpty).

Definition Exec_STSLICER : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STSLICER TVMBitStringEmpty ).

Definition Exec_STSLICER' : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STSLICER TVMBitStringEmpty ).

Definition Exec_STU (i: TVMBitString): TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STU i).

Definition Exec_STU' (i: TVMBitString): TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STU' i).

Definition Exec_STUR (i: TVMBitString): TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STUR i).

Definition Exec_STUR' (i: TVMBitString): TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STUR' i).

Definition Exec_STZEROES : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STZEROES TVMBitStringEmpty).

Definition Exec_STZEROES' : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_STZEROES TVMBitStringEmpty).

Definition Exec_SUB : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SUB TVMBitStringEmpty).

Definition Exec_SUBR : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SUBR TVMBitStringEmpty ).

Definition Exec_THIRD : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_THIRD TVMBitStringEmpty).

Definition Exec_THROWANY : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_THROWANY TVMBitStringEmpty).

Definition Exec_THROWIF(i: TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_THROWIF i).

Definition Exec_THROWIFNOT(i: TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_THROWIFNOT i).

Definition Exec_TPUSH : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_TPUSH TVMBitStringEmpty).

Definition Exec_TUPLE (i: TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_TUPLE i).

Definition Exec_UFITS (i: TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_UFITS i).

Definition Exec_UFITS' (i: TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_UFITS' i).

Definition Exec_UNTIL (* (i: TVMBitString) *): TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_UNTIL TVMBitStringEmpty tvmSliceEmpty st);
   put st'; void!.

Definition Exec_XCHG (i: TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_XCHG i).

Definition Exec_DUP: TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DUP).

Definition Exec_SWAP: TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SWAP).

Definition Exec_SWAP2: TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SWAP2).

Definition Exec_LTIME : TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_LTIME tvmSliceEmpty st);
   put st'; void!.

Definition Exec_NOW : TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_NOW tvmSliceEmpty st);
   put st'; void!.

Definition Exec_NIP: TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NIP).

Definition Exec_PUSHCONT (i: list (TVMStateT True)): TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PUSHINT80 (Z2IBS 8 100)).

Definition Exec_UNPAIR : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_UNPAIR TVMBitStringEmpty).

Definition Exec_FALSE : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PUSHINT7 x0H).

Definition Exec_TRUE : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PUSHINT7 xFH).

Definition Exec_CALLX : TVMStateT True :=
Exec_EXECUTE TVMBitStringEmpty.

Definition Exec_COMMIT : TVMStateT True :=
Exec_NOP.

Definition Exec_DICTUMIN : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DICTUMIN TVMBitStringEmpty).

Definition Exec_HASHCU  : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_HASHCU TVMBitStringEmpty).

Definition Exec_REVERSE (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_REVERSE i).

Definition Exec_SCUTFIRST (i : TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_SCUTFIRST i).

(***************)


Definition Exec_CALL(i: TVMBitString): TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_CALL i tvmSliceEmpty st);
   put st'; void!.

Definition Exec_CALLDICT (i: TVMBitString): TVMStateT True :=
Exec_CALL i.

Definition Exec_CHKSIGNU : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_CHKSIGNU TVMBitStringEmpty).

Definition Exec_CHKSIGNU_NO : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_CHKSIGNU_NO TVMBitStringEmpty).

Definition Exec_LDMSGADDR : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_LDMSGADDR TVMBitStringEmpty).

Definition Exec_PARSEMSGADDR: TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PARSEMSGADDR TVMBitStringEmpty).

Definition Exec_PUSHREFCONT: TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_PUSHREFCONT TVMBitStringEmpty tvmSliceEmpty st);
   put st'; void!.

Definition Exec_SENDRAWMSG: TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_SENDRAWMSG TVMBitStringEmpty tvmSliceEmpty st);
   put st'; void!.

Definition Exec_SETCODE: TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_SETCODE TVMBitStringEmpty tvmSliceEmpty st);
   put st'; void!.


Definition Exec_DEPTH : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_DEPTH TVMBitStringEmpty ).

Definition Exec_PICK : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PICK TVMBitStringEmpty ).

Definition Exec_PAIR : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_PAIR ).

Definition Exec_MYADDR: TVMStateT True :=
do st ← get (T:=StateT);
do st' ← lift (exec_MYADDR tvmSliceEmpty st);
   put st'; void!. 
(******************* Некие затычки ***************************)
Definition Exec_BLKPUSH (i: TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NOP).
Definition Exec_GETGLOB (i: TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NOP).
Definition Exec_SETGLOB (i: TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NOP). 
Definition Exec_STSLICECONST (i: TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NOP).
Definition Exec_STB : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NOP).
Definition Exec_UNTUPLE (i: TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NOP).
Definition Exec_DICTEMPTY : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NOP).
Definition Exec_LDMSGADDRQ : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NOP).
Definition Exec_LDUQ (i: TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NOP).
Definition Exec_PUSH3 (i: TVMBitString) : TVMStateT True :=
↑ stackFunctionStateEmbed (exec_NOP).

(*************************************************************)

Definition convert82 (z :Z) :=
let l := degreePos0 z + 1 in
let l1 := ((l - 19) / 8) + 1 in
let lpart := pos2IBS 5 (Pos.of_nat l1) in 
tvmBitStringCombine lpart (Z2IBS (( 8*l1) + 19) z).

Definition Exec_PUSHINTz (z: Z) :=
if (andb (z>=?-5)%Z (z<=?10)%Z) then Exec_PUSHINT7 (Z2IBS 4 z) else 
if (andb (z>=?-128)%Z (z<=?127)%Z) then Exec_PUSHINT80 (Z2IBS 8 z) else
if (andb (z>=?-32768)%Z (z<=?32767)%Z) then Exec_PUSHINT81 (Z2IBS 32 z)
                                       else Exec_PUSHINT82 (convert82 z).                                      

(*check bit number*)
Definition Exec_LDSLICEz (z:Z) := Exec_LDSLICE (Z2IBS 16 (z - 1)).
Definition Exec_BLKDROPz (z:Z) := Exec_BLKDROP (Z2IBS 4 z).
Definition Exec_PLDUz    (z:Z) := Exec_PLDU (Z2IBS 16 (z - 1)).
Definition Exec_PLDU'z    (z:Z) := Exec_PLDU' (Z2IBS 16 (z - 1)).
Definition Exec_LDUz     (z:Z) := Exec_LDU (Z2IBS 16 (z - 1)).
Definition Exec_LDU'z     (z:Z) := Exec_LDU' (Z2IBS 16 (z - 1)).
Definition Exec_THROWIFz (z: Z) : TVMStateT True := Exec_THROWIF (Z2IBS 8 z).
Definition Exec_THROWIFNOTz (z: Z) : TVMStateT True := Exec_THROWIFNOT (Z2IBS 8 z).
Definition Exec_BLKSWAPz    (z1 z2: Z) : TVMStateT True := Exec_BLKSWAP (tvmBitStringCombine (Z2IBS 4 (z1 -1)) (Z2IBS 4 (z2 - 1))).

Definition Exec_STURz   (z: Z): TVMStateT True := Exec_STUR (Z2IBS 8 (z - 1)).
Definition Exec_STUz    (z: Z): TVMStateT True := Exec_STU (Z2IBS 8 (z - 1)).

Definition Exec_STUR'z   (z: Z): TVMStateT True := Exec_STUR' (Z2IBS 8 (z - 1)).
Definition Exec_STU'z    (z: Z): TVMStateT True := Exec_STU' (Z2IBS 8 (z - 1)).

Definition Exec_LDIz    (z: Z): TVMStateT True := Exec_LDI (Z2IBS 8 (z - 1)).  
Definition Exec_LDI'z    (z: Z): TVMStateT True := Exec_LDI' (Z2IBS 8 (z - 1)).  

Definition Exec_INDEXz  (z: Z): TVMStateT True := Exec_INDEX (Z2IBS 4 z).  
Definition Exec_PLDREFIDXz (z: Z): TVMStateT True := Exec_PLDREFIDX (Z2IBS 4 z). 
Definition Exec_REVERSEz   (z1 z2: Z) : TVMStateT True := Exec_REVERSE (tvmBitStringCombine (Z2IBS 4 z1) (Z2IBS 4 z2)).
Definition Exec_UFITSz     (z: Z): TVMStateT True := Exec_UFITS (Z2IBS 8 (z - 1)).
Definition Exec_UFITS'z     (z: Z): TVMStateT True := Exec_UFITS' (Z2IBS 8 (z - 1)). 
Definition Exec_PUSHPOW2DECz (z: Z): TVMStateT True := Exec_PUSHPOW2DEC (Z2IBS 8 z). 
Definition Exec_EQINTz    (z: Z): TVMStateT True := Exec_EQINT (Z2IBS 256 z). 
Definition Exec_STIz      (z: Z): TVMStateT True := Exec_STI (Z2IBS 8 (z - 1)).
Definition Exec_STI'z      (z: Z): TVMStateT True := Exec_STI' (Z2IBS 8 (z - 1)). 
Definition Exec_STIRz     (z: Z): TVMStateT True := Exec_STIR (Z2IBS 8 (z - 1)). 
Definition Exec_STIR'z     (z: Z): TVMStateT True := Exec_STIR' (Z2IBS 8 (z - 1)). 
Definition Exec_LESSINTz  (z: Z): TVMStateT True := Exec_LESSINT (Z2IBS 256 z).
Definition Exec_GETPARAMz (z: Z): TVMStateT True := Exec_GETPARAM (Z2IBS 256 z).
Definition Exec_throw x : TVMStateT True := lift (throw True x).
Definition Exec_CALLz (z: Z): TVMStateT True := Exec_CALL (Z2IBS 256 z).
Definition Exec_NEQINTz (z: Z): TVMStateT True := Exec_NEQINT (Z2IBS 256 z).
Definition Exec_PLDIz (z: Z): TVMStateT True := Exec_PLDI (Z2IBS 256 (z - 1)).
Definition Exec_PLDI'z (z: Z): TVMStateT True := Exec_PLDI' (Z2IBS 256 (z - 1)).
Definition Exec_GTINTz (z: Z): TVMStateT True := Exec_GTINT (Z2IBS 256 z).
(**************  THE FAKES   *************************)
Definition Exec_WHILE: TVMStateT True := return! I.
Definition Exec_JMPX:  TVMStateT True  := return! I.

Definition Exec_BLKPUSHzz (z1 z2:Z) : TVMStateT True := Exec_BLKPUSH (Z2IBS 256 (z1+z2)).
Definition Exec_GETGLOBz (z: Z): TVMStateT True := Exec_GETGLOB (Z2IBS 256 z).
Definition Exec_SETGLOBz (z: Z): TVMStateT True := Exec_SETGLOB (Z2IBS 256 z).
Definition Exec_SETINDEXz (z: Z): TVMStateT True := Exec_SETINDEX (Z2IBS 256 z).
Definition Exec_STSLICECONSTz (z: Z): TVMStateT True := Exec_STSLICECONST (Z2IBS 256 z).
Definition Exec_STSLICECONSTs (s:string): TVMStateT True := Exec_STSLICECONST (Z2IBS 256    0    ).
Definition Exec_PUSH2ss (z1 z2: string) : TVMStateT True := Exec_PUSH2 (Z2IBS 4 1).
Definition Exec_PUSH3sss (z1 z2 z3: string) : TVMStateT True := Exec_PUSH3 (Z2IBS 4 1).
Definition Exec_TUPLEz (z: Z): TVMStateT True := Exec_TUPLE (Z2IBS 256 z).
Definition Exec_UNTUPLEz (z: Z): TVMStateT True := Exec_UNTUPLE (Z2IBS 256 z).
Definition Exec_LDUQz (z: Z): TVMStateT True := Exec_LDUQ (Z2IBS 256 z).


Definition exec_LDMSGADDR_stub (address: TVMBitString) rest (s : TVMStack) : OpResultContainer TVMStack :=
opNormal _ (cons  rest
 (replaceStack 0 s (State._TVMSlice (_TVMSlice address nil)) )).

Definition Exec_LDMSGADDR_stub (address: TVMBitString) rest : TVMStateT True :=
↑  stackFunctionStateEmbed (exec_LDMSGADDR_stub address rest).

Definition tvm_ifelse (x y: TVMStateT True) : TVMStateT True :=
do st ← get (T:=StateT);
let stack := contStack (tvmCC st) in
if (List.length stack <? 1) then Exec_throw (STACK_UNDERFLOW_EXCEPTION NULL_PARAM) else
match (stackIndex 0%nat stack) with
  |  State._TVMInteger i => Exec_DROP >> (if (andb (tvmNotNan 257 i) (I2ZN 257 i =? 0)%Z) then y else x)
  | _  => Exec_throw (TYPE_CHECK_EXCEPTION NULL_PARAM)
end.

Definition tvm_call_inline (f: TVMStateT True) : TVMStateT True := f.

Definition tvm_until (f: TVMStateT True) : TVMStateT True := f >> Exec_DROP.
Definition tvm_while (a f: TVMStateT True) : TVMStateT True := a >> tvm_ifelse f (return! I).

Definition sample1_exec :=
Exec_PUSHCTR7 >>
Exec_DUP  >> 
Exec_SECOND >>
Exec_PUSHINT7 x5H >>
Exec_NEWC >>
Exec_STUz 8 >>
Exec_PUSHINT80 (tvmBitStringCombine x6H x4H) >>
Exec_ROT >>
Exec_PUSHINT80 (tvmBitStringCombine x4H x0H) >>
Exec_DICTUSETB >>
Exec_SETSECOND >>
Exec_POPCTR7.

Set Typeclasses Iterative Deepening.
Set Typeclasses Depth 100.

Existing Instance idMonad_Monad.

(**********************************************************************)


Export ListNotations.
(* Export C.Notations. *)

Local Open Scope string_scope.
Local Open Scope list_scope.

Definition newline := String "010"%char "".

(* Compute split_string ("a b c"++(String "010"%char "") ++ "xxx") (String "010"%char "").
Compute split_string ("a b      c") " ". *)

Definition isComment := prefix ";".


Definition readTVMCmd (code: string): list string :=
if (isComment code) then [ ] 
else
let codeSplitted :=  split_string code " " in
let trimmed := filter (fun s => negb (isBlank s) ) codeSplitted in
trimmed.

Inductive ParseType := Command | Arg.

Inductive TVMCommandSignature := 
| TVMNoArgs     :   TVMStateT True -> TVMCommandSignature
| TVMZ1Args     : ( Z -> TVMStateT True ) -> TVMCommandSignature
| TVMZ2Args     : ( Z -> Z -> TVMStateT True ) -> TVMCommandSignature
| TVMBS1Args    : ( TVMBitString -> TVMStateT True ) -> TVMCommandSignature
| TVMSlice1Args : ( TVMSlice -> TVMStateT True ) -> TVMCommandSignature
| TVM2Args      : ( TVMBitString -> TVMSlice -> TVMStateT True ) -> TVMCommandSignature
| TVMCode1Args  : ( list (TVMStateT True) -> TVMStateT True ) -> TVMCommandSignature
| TVMEndCont    :   TVMCommandSignature
| TVMStr1Args   : ( string -> TVMStateT True ) -> TVMCommandSignature.  

Record TVMCommand := {
       name: string;
       tvmCommand: TVMCommandSignature}.

Definition Exec_PUSHs (s : string) :=
if (orb (String.eqb s "S1") (String.eqb s "s1")) then Exec_PUSH (Z2IBS 4 1) else
if (orb (String.eqb s "S2") (String.eqb s "s2")) then Exec_PUSH (Z2IBS 4 2) else
if (orb (String.eqb s "S3") (String.eqb s "s3")) then Exec_PUSH (Z2IBS 4 3) else
if (orb (String.eqb s "S4") (String.eqb s "s4")) then Exec_PUSH (Z2IBS 4 4) else
if (orb (String.eqb s "S5") (String.eqb s "s5")) then Exec_PUSH (Z2IBS 4 5) else
if (orb (String.eqb s "S6") (String.eqb s "s6")) then Exec_PUSH (Z2IBS 4 6) else
if (orb (String.eqb s "S7") (String.eqb s "s7")) then Exec_PUSH (Z2IBS 4 7) else
if (orb (String.eqb s "S8") (String.eqb s "s8")) then Exec_PUSH (Z2IBS 4 8) else
if (orb (String.eqb s "S9") (String.eqb s "s9")) then Exec_PUSH (Z2IBS 4 9) else
if (orb (String.eqb s "S10") (String.eqb s "s10")) then Exec_PUSH (Z2IBS 4 10) else
if (orb (String.eqb s "S11") (String.eqb s "s11")) then Exec_PUSH (Z2IBS 4 11) else
if (orb (String.eqb s "S12") (String.eqb s "s12")) then Exec_PUSH (Z2IBS 4 12) else
if (orb (String.eqb s "S13") (String.eqb s "s13")) then Exec_PUSH (Z2IBS 4 13) else
if (orb (String.eqb s "S14") (String.eqb s "s14")) then Exec_PUSH (Z2IBS 4 14) else
if (orb (String.eqb s "S15") (String.eqb s "s15")) then Exec_PUSH (Z2IBS 4 15) else

if (orb (String.eqb s "C7") (String.eqb s "c7")) then Exec_PUSHCTR7  else
if (orb (String.eqb s "C4") (String.eqb s "c4")) then Exec_PUSHROOT  else
return! I.

Definition Exec_PUSHCTRs (s : string) :=
if (orb (String.eqb s "C7") (String.eqb s "c7")) then Exec_PUSHCTR7  else
if (orb (String.eqb s "C4") (String.eqb s "c4")) then Exec_PUSHROOT  else
return! I.

Definition Exec_POPs (s : string) :=
if (orb (String.eqb s "S1") (String.eqb s "s1")) then Exec_POP (Z2IBS 4 1) else
if (orb (String.eqb s "S2") (String.eqb s "s2")) then Exec_POP (Z2IBS 4 2) else
if (orb (String.eqb s "S3") (String.eqb s "s3")) then Exec_POP (Z2IBS 4 3) else
if (orb (String.eqb s "S4") (String.eqb s "s4")) then Exec_POP (Z2IBS 4 4) else
if (orb (String.eqb s "S5") (String.eqb s "s5")) then Exec_POP (Z2IBS 4 5) else
if (orb (String.eqb s "S6") (String.eqb s "s6")) then Exec_POP (Z2IBS 4 6) else
if (orb (String.eqb s "S7") (String.eqb s "s7")) then Exec_POP (Z2IBS 4 7) else
if (orb (String.eqb s "S8") (String.eqb s "s8")) then Exec_POP (Z2IBS 4 8) else
if (orb (String.eqb s "S9") (String.eqb s "s9")) then Exec_POP (Z2IBS 4 9) else
if (orb (String.eqb s "S10") (String.eqb s "s10")) then Exec_POP (Z2IBS 4 10) else
if (orb (String.eqb s "S11") (String.eqb s "s11")) then Exec_POP (Z2IBS 4 11) else
if (orb (String.eqb s "S12") (String.eqb s "s12")) then Exec_POP (Z2IBS 4 12) else
if (orb (String.eqb s "S13") (String.eqb s "s13")) then Exec_POP (Z2IBS 4 13) else
if (orb (String.eqb s "S14") (String.eqb s "s14")) then Exec_POP (Z2IBS 4 14) else
if (orb (String.eqb s "S15") (String.eqb s "s15")) then Exec_POP (Z2IBS 4 15) else

if (orb (String.eqb s "C4") (String.eqb s "c4")) then Exec_POPROOT else
if (orb (String.eqb s "C7") (String.eqb s "c7")) then Exec_POPCTR7 else
return! I.

Definition Exec_POPCTRs (s : string) :=
if (orb (String.eqb s "C7") (String.eqb s "c7")) then Exec_POPCTR7  else
if (orb (String.eqb s "C4") (String.eqb s "c4")) then Exec_POPROOT  else
return! I.

Definition Z2Z2IBS(a:nat)(b:Z)(c:nat)(d:Z) :=
Z2IBS 8 (b + d).

(* Check Z2Z2IBS. *)

Definition Exec_XCHGs (s : string) :=
if (orb (String.eqb s "s0") (String.eqb s "S0")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 0 ) else
if (orb (String.eqb s "s1") (String.eqb s "S1")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 1 ) else
if (orb (String.eqb s "s2") (String.eqb s "S2")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 2 ) else
if (orb (String.eqb s "s3") (String.eqb s "S3")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 3 ) else
if (orb (String.eqb s "s4") (String.eqb s "S4")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 4 ) else
if (orb (String.eqb s "s5") (String.eqb s "S5")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 5 ) else
if (orb (String.eqb s "s6") (String.eqb s "S6")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 6 ) else
if (orb (String.eqb s "s7") (String.eqb s "S7")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 7 ) else
if (orb (String.eqb s "s8") (String.eqb s "S8")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 8 ) else
if (orb (String.eqb s "s9") (String.eqb s "S9")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 9 ) else
if (orb (String.eqb s "s10") (String.eqb s "S10")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 10 ) else
if (orb (String.eqb s "s11") (String.eqb s "S11")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 11 ) else
if (orb (String.eqb s "s12") (String.eqb s "S12")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 12 ) else
if (orb (String.eqb s "s13") (String.eqb s "S13")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 13 ) else
if (orb (String.eqb s "s14") (String.eqb s "S14")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 14 ) else
if (orb (String.eqb s "s15") (String.eqb s "S15")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 15 ) else

if (orb (String.eqb s "s0,s0") (String.eqb s "S0,S0")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 0 ) else
if (orb (String.eqb s "s1,s0") (String.eqb s "S1,S0")) then Exec_XCHG    ( Z2Z2IBS  4 1   4 0 ) else
if (orb (String.eqb s "s2,s0") (String.eqb s "S2,S0")) then Exec_XCHG    ( Z2Z2IBS  4 2   4 0 ) else
if (orb (String.eqb s "s3,s0") (String.eqb s "S3,S0")) then Exec_XCHG    ( Z2Z2IBS  4 3   4 0 ) else
if (orb (String.eqb s "s4,s0") (String.eqb s "S4,S0")) then Exec_XCHG    ( Z2Z2IBS  4 4   4 0 ) else
if (orb (String.eqb s "s5,s0") (String.eqb s "S5,S0")) then Exec_XCHG    ( Z2Z2IBS  4 5   4 0 ) else
if (orb (String.eqb s "s6,s0") (String.eqb s "S6,S0")) then Exec_XCHG    ( Z2Z2IBS  4 6   4 0 ) else
if (orb (String.eqb s "s7,s0") (String.eqb s "S7,S0")) then Exec_XCHG    ( Z2Z2IBS  4 7   4 0 ) else
if (orb (String.eqb s "s8,s0") (String.eqb s "S8,S0")) then Exec_XCHG    ( Z2Z2IBS  4 8   4 0 ) else
if (orb (String.eqb s "s9,s0") (String.eqb s "S9,S0")) then Exec_XCHG    ( Z2Z2IBS  4 9   4 0 ) else
if (orb (String.eqb s "s10,s0") (String.eqb s "S10,S0")) then Exec_XCHG    ( Z2Z2IBS  4 10   4 0 ) else
if (orb (String.eqb s "s11,s0") (String.eqb s "S11,S0")) then Exec_XCHG    ( Z2Z2IBS  4 11   4 0 ) else
if (orb (String.eqb s "s12,s0") (String.eqb s "S12,S0")) then Exec_XCHG    ( Z2Z2IBS  4 12   4 0 ) else
if (orb (String.eqb s "s13,s0") (String.eqb s "S13,S0")) then Exec_XCHG    ( Z2Z2IBS  4 13   4 0 ) else
if (orb (String.eqb s "s14,s0") (String.eqb s "S14,S0")) then Exec_XCHG    ( Z2Z2IBS  4 14   4 0 ) else
if (orb (String.eqb s "s15,s0") (String.eqb s "S15,S0")) then Exec_XCHG    ( Z2Z2IBS  4 15   4 0 ) else

if (orb (String.eqb s "s0,s1") (String.eqb s "S0,S1")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 1 ) else
if (orb (String.eqb s "s1,s1") (String.eqb s "S1,S1")) then Exec_XCHG    ( Z2Z2IBS  4 1   4 1 ) else
if (orb (String.eqb s "s2,s1") (String.eqb s "S2,S1")) then Exec_XCHG    ( Z2Z2IBS  4 2   4 1 ) else
if (orb (String.eqb s "s3,s1") (String.eqb s "S3,S1")) then Exec_XCHG    ( Z2Z2IBS  4 3   4 1 ) else
if (orb (String.eqb s "s4,s1") (String.eqb s "S4,S1")) then Exec_XCHG    ( Z2Z2IBS  4 4   4 1 ) else
if (orb (String.eqb s "s5,s1") (String.eqb s "S5,S1")) then Exec_XCHG    ( Z2Z2IBS  4 5   4 1 ) else
if (orb (String.eqb s "s6,s1") (String.eqb s "S6,S1")) then Exec_XCHG    ( Z2Z2IBS  4 6   4 1 ) else
if (orb (String.eqb s "s7,s1") (String.eqb s "S7,S1")) then Exec_XCHG    ( Z2Z2IBS  4 7   4 1 ) else
if (orb (String.eqb s "s8,s1") (String.eqb s "S8,S1")) then Exec_XCHG    ( Z2Z2IBS  4 8   4 1 ) else
if (orb (String.eqb s "s9,s1") (String.eqb s "S9,S1")) then Exec_XCHG    ( Z2Z2IBS  4 9   4 1 ) else
if (orb (String.eqb s "s10,s1") (String.eqb s "S10,S1")) then Exec_XCHG    ( Z2Z2IBS  4 10   4 1 ) else
if (orb (String.eqb s "s11,s1") (String.eqb s "S11,S1")) then Exec_XCHG    ( Z2Z2IBS  4 11   4 1 ) else
if (orb (String.eqb s "s12,s1") (String.eqb s "S12,S1")) then Exec_XCHG    ( Z2Z2IBS  4 12   4 1 ) else
if (orb (String.eqb s "s13,s1") (String.eqb s "S13,S1")) then Exec_XCHG    ( Z2Z2IBS  4 13   4 1 ) else
if (orb (String.eqb s "s14,s1") (String.eqb s "S14,S1")) then Exec_XCHG    ( Z2Z2IBS  4 14   4 1 ) else
if (orb (String.eqb s "s15,s1") (String.eqb s "S15,S1")) then Exec_XCHG    ( Z2Z2IBS  4 15   4 1 ) else

if (orb (String.eqb s "s0,s2") (String.eqb s "S0,S2")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 2 ) else
if (orb (String.eqb s "s1,s2") (String.eqb s "S1,S2")) then Exec_XCHG    ( Z2Z2IBS  4 1   4 2 ) else
if (orb (String.eqb s "s2,s2") (String.eqb s "S2,S2")) then Exec_XCHG    ( Z2Z2IBS  4 2   4 2 ) else
if (orb (String.eqb s "s3,s2") (String.eqb s "S3,S2")) then Exec_XCHG    ( Z2Z2IBS  4 3   4 2 ) else
if (orb (String.eqb s "s4,s2") (String.eqb s "S4,S2")) then Exec_XCHG    ( Z2Z2IBS  4 4   4 2 ) else
if (orb (String.eqb s "s5,s2") (String.eqb s "S5,S2")) then Exec_XCHG    ( Z2Z2IBS  4 5   4 2 ) else
if (orb (String.eqb s "s6,s2") (String.eqb s "S6,S2")) then Exec_XCHG    ( Z2Z2IBS  4 6   4 2 ) else
if (orb (String.eqb s "s7,s2") (String.eqb s "S7,S2")) then Exec_XCHG    ( Z2Z2IBS  4 7   4 2 ) else
if (orb (String.eqb s "s8,s2") (String.eqb s "S8,S2")) then Exec_XCHG    ( Z2Z2IBS  4 8   4 2 ) else
if (orb (String.eqb s "s9,s2") (String.eqb s "S9,S2")) then Exec_XCHG    ( Z2Z2IBS  4 9   4 2 ) else
if (orb (String.eqb s "s10,s2") (String.eqb s "S10,S2")) then Exec_XCHG    ( Z2Z2IBS  4 10   4 2 ) else
if (orb (String.eqb s "s11,s2") (String.eqb s "S11,S2")) then Exec_XCHG    ( Z2Z2IBS  4 11   4 2 ) else
if (orb (String.eqb s "s12,s2") (String.eqb s "S12,S2")) then Exec_XCHG    ( Z2Z2IBS  4 12   4 2 ) else
if (orb (String.eqb s "s13,s2") (String.eqb s "S13,S2")) then Exec_XCHG    ( Z2Z2IBS  4 13   4 2 ) else
if (orb (String.eqb s "s14,s2") (String.eqb s "S14,S2")) then Exec_XCHG    ( Z2Z2IBS  4 14   4 2 ) else
if (orb (String.eqb s "s15,s2") (String.eqb s "S15,S2")) then Exec_XCHG    ( Z2Z2IBS  4 15   4 2 ) else

if (orb (String.eqb s "s0,s3") (String.eqb s "S0,S3")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 3 ) else
if (orb (String.eqb s "s1,s3") (String.eqb s "S1,S3")) then Exec_XCHG    ( Z2Z2IBS  4 1   4 3 ) else
if (orb (String.eqb s "s2,s3") (String.eqb s "S2,S3")) then Exec_XCHG    ( Z2Z2IBS  4 2   4 3 ) else
if (orb (String.eqb s "s3,s3") (String.eqb s "S3,S3")) then Exec_XCHG    ( Z2Z2IBS  4 3   4 3 ) else
if (orb (String.eqb s "s4,s3") (String.eqb s "S4,S3")) then Exec_XCHG    ( Z2Z2IBS  4 4   4 3 ) else
if (orb (String.eqb s "s5,s3") (String.eqb s "S5,S3")) then Exec_XCHG    ( Z2Z2IBS  4 5   4 3 ) else
if (orb (String.eqb s "s6,s3") (String.eqb s "S6,S3")) then Exec_XCHG    ( Z2Z2IBS  4 6   4 3 ) else
if (orb (String.eqb s "s7,s3") (String.eqb s "S7,S3")) then Exec_XCHG    ( Z2Z2IBS  4 7   4 3 ) else
if (orb (String.eqb s "s8,s3") (String.eqb s "S8,S3")) then Exec_XCHG    ( Z2Z2IBS  4 8   4 3 ) else
if (orb (String.eqb s "s9,s3") (String.eqb s "S9,S3")) then Exec_XCHG    ( Z2Z2IBS  4 9   4 3 ) else
if (orb (String.eqb s "s10,s3") (String.eqb s "S10,S3")) then Exec_XCHG    ( Z2Z2IBS  4 10   4 3 ) else
if (orb (String.eqb s "s11,s3") (String.eqb s "S11,S3")) then Exec_XCHG    ( Z2Z2IBS  4 11   4 3 ) else
if (orb (String.eqb s "s12,s3") (String.eqb s "S12,S3")) then Exec_XCHG    ( Z2Z2IBS  4 12   4 3 ) else
if (orb (String.eqb s "s13,s3") (String.eqb s "S13,S3")) then Exec_XCHG    ( Z2Z2IBS  4 13   4 3 ) else
if (orb (String.eqb s "s14,s3") (String.eqb s "S14,S3")) then Exec_XCHG    ( Z2Z2IBS  4 14   4 3 ) else
if (orb (String.eqb s "s15,s3") (String.eqb s "S15,S3")) then Exec_XCHG    ( Z2Z2IBS  4 15   4 3 ) else

if (orb (String.eqb s "s0,s4") (String.eqb s "S0,S4")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 4 ) else
if (orb (String.eqb s "s1,s4") (String.eqb s "S1,S4")) then Exec_XCHG    ( Z2Z2IBS  4 1   4 4 ) else
if (orb (String.eqb s "s2,s4") (String.eqb s "S2,S4")) then Exec_XCHG    ( Z2Z2IBS  4 2   4 4 ) else
if (orb (String.eqb s "s3,s4") (String.eqb s "S3,S4")) then Exec_XCHG    ( Z2Z2IBS  4 3   4 4 ) else
if (orb (String.eqb s "s4,s4") (String.eqb s "S4,S4")) then Exec_XCHG    ( Z2Z2IBS  4 4   4 4 ) else
if (orb (String.eqb s "s5,s4") (String.eqb s "S5,S4")) then Exec_XCHG    ( Z2Z2IBS  4 5   4 4 ) else
if (orb (String.eqb s "s6,s4") (String.eqb s "S6,S4")) then Exec_XCHG    ( Z2Z2IBS  4 6   4 4 ) else
if (orb (String.eqb s "s7,s4") (String.eqb s "S7,S4")) then Exec_XCHG    ( Z2Z2IBS  4 7   4 4 ) else
if (orb (String.eqb s "s8,s4") (String.eqb s "S8,S4")) then Exec_XCHG    ( Z2Z2IBS  4 8   4 4 ) else
if (orb (String.eqb s "s9,s4") (String.eqb s "S9,S4")) then Exec_XCHG    ( Z2Z2IBS  4 9   4 4 ) else
if (orb (String.eqb s "s10,s4") (String.eqb s "S10,S4")) then Exec_XCHG    ( Z2Z2IBS  4 10   4 4 ) else
if (orb (String.eqb s "s11,s4") (String.eqb s "S11,S4")) then Exec_XCHG    ( Z2Z2IBS  4 11   4 4 ) else
if (orb (String.eqb s "s12,s4") (String.eqb s "S12,S4")) then Exec_XCHG    ( Z2Z2IBS  4 12   4 4 ) else
if (orb (String.eqb s "s13,s4") (String.eqb s "S13,S4")) then Exec_XCHG    ( Z2Z2IBS  4 13   4 4 ) else
if (orb (String.eqb s "s14,s4") (String.eqb s "S14,S4")) then Exec_XCHG    ( Z2Z2IBS  4 14   4 4 ) else
if (orb (String.eqb s "s15,s4") (String.eqb s "S15,S4")) then Exec_XCHG    ( Z2Z2IBS  4 15   4 4 ) else

if (orb (String.eqb s "s0,s5") (String.eqb s "S0,S5")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 5 ) else
if (orb (String.eqb s "s1,s5") (String.eqb s "S1,S5")) then Exec_XCHG    ( Z2Z2IBS  4 1   4 5 ) else
if (orb (String.eqb s "s2,s5") (String.eqb s "S2,S5")) then Exec_XCHG    ( Z2Z2IBS  4 2   4 5 ) else
if (orb (String.eqb s "s3,s5") (String.eqb s "S3,S5")) then Exec_XCHG    ( Z2Z2IBS  4 3   4 5 ) else
if (orb (String.eqb s "s4,s5") (String.eqb s "S4,S5")) then Exec_XCHG    ( Z2Z2IBS  4 4   4 5 ) else
if (orb (String.eqb s "s5,s5") (String.eqb s "S5,S5")) then Exec_XCHG    ( Z2Z2IBS  4 5   4 5 ) else
if (orb (String.eqb s "s6,s5") (String.eqb s "S6,S5")) then Exec_XCHG    ( Z2Z2IBS  4 6   4 5 ) else
if (orb (String.eqb s "s7,s5") (String.eqb s "S7,S5")) then Exec_XCHG    ( Z2Z2IBS  4 7   4 5 ) else
if (orb (String.eqb s "s8,s5") (String.eqb s "S8,S5")) then Exec_XCHG    ( Z2Z2IBS  4 8   4 5 ) else
if (orb (String.eqb s "s9,s5") (String.eqb s "S9,S5")) then Exec_XCHG    ( Z2Z2IBS  4 9   4 5 ) else
if (orb (String.eqb s "s10,s5") (String.eqb s "S10,S5")) then Exec_XCHG    ( Z2Z2IBS  4 10   4 5 ) else
if (orb (String.eqb s "s11,s5") (String.eqb s "S11,S5")) then Exec_XCHG    ( Z2Z2IBS  4 11   4 5 ) else
if (orb (String.eqb s "s12,s5") (String.eqb s "S12,S5")) then Exec_XCHG    ( Z2Z2IBS  4 12   4 5 ) else
if (orb (String.eqb s "s13,s5") (String.eqb s "S13,S5")) then Exec_XCHG    ( Z2Z2IBS  4 13   4 5 ) else
if (orb (String.eqb s "s14,s5") (String.eqb s "S14,S5")) then Exec_XCHG    ( Z2Z2IBS  4 14   4 5 ) else
if (orb (String.eqb s "s15,s5") (String.eqb s "S15,S5")) then Exec_XCHG    ( Z2Z2IBS  4 15   4 5 ) else

if (orb (String.eqb s "s0,s6") (String.eqb s "S0,S6")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 6 ) else
if (orb (String.eqb s "s1,s6") (String.eqb s "S1,S6")) then Exec_XCHG    ( Z2Z2IBS  4 1   4 6 ) else
if (orb (String.eqb s "s2,s6") (String.eqb s "S2,S6")) then Exec_XCHG    ( Z2Z2IBS  4 2   4 6 ) else
if (orb (String.eqb s "s3,s6") (String.eqb s "S3,S6")) then Exec_XCHG    ( Z2Z2IBS  4 3   4 6 ) else
if (orb (String.eqb s "s4,s6") (String.eqb s "S4,S6")) then Exec_XCHG    ( Z2Z2IBS  4 4   4 6 ) else
if (orb (String.eqb s "s5,s6") (String.eqb s "S5,S6")) then Exec_XCHG    ( Z2Z2IBS  4 5   4 6 ) else
if (orb (String.eqb s "s6,s6") (String.eqb s "S6,S6")) then Exec_XCHG    ( Z2Z2IBS  4 6   4 6 ) else
if (orb (String.eqb s "s7,s6") (String.eqb s "S7,S6")) then Exec_XCHG    ( Z2Z2IBS  4 7   4 6 ) else
if (orb (String.eqb s "s8,s6") (String.eqb s "S8,S6")) then Exec_XCHG    ( Z2Z2IBS  4 8   4 6 ) else
if (orb (String.eqb s "s9,s6") (String.eqb s "S9,S6")) then Exec_XCHG    ( Z2Z2IBS  4 9   4 6 ) else
if (orb (String.eqb s "s10,s6") (String.eqb s "S10,S6")) then Exec_XCHG    ( Z2Z2IBS  4 10   4 6 ) else
if (orb (String.eqb s "s11,s6") (String.eqb s "S11,S6")) then Exec_XCHG    ( Z2Z2IBS  4 11   4 6 ) else
if (orb (String.eqb s "s12,s6") (String.eqb s "S12,S6")) then Exec_XCHG    ( Z2Z2IBS  4 12   4 6 ) else
if (orb (String.eqb s "s13,s6") (String.eqb s "S13,S6")) then Exec_XCHG    ( Z2Z2IBS  4 13   4 6 ) else
if (orb (String.eqb s "s14,s6") (String.eqb s "S14,S6")) then Exec_XCHG    ( Z2Z2IBS  4 14   4 6 ) else
if (orb (String.eqb s "s15,s6") (String.eqb s "S15,S6")) then Exec_XCHG    ( Z2Z2IBS  4 15   4 6 ) else

if (orb (String.eqb s "s0,s7") (String.eqb s "S0,S7")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 7 ) else
if (orb (String.eqb s "s1,s7") (String.eqb s "S1,S7")) then Exec_XCHG    ( Z2Z2IBS  4 1   4 7 ) else
if (orb (String.eqb s "s2,s7") (String.eqb s "S2,S7")) then Exec_XCHG    ( Z2Z2IBS  4 2   4 7 ) else
if (orb (String.eqb s "s3,s7") (String.eqb s "S3,S7")) then Exec_XCHG    ( Z2Z2IBS  4 3   4 7 ) else
if (orb (String.eqb s "s4,s7") (String.eqb s "S4,S7")) then Exec_XCHG    ( Z2Z2IBS  4 4   4 7 ) else
if (orb (String.eqb s "s5,s7") (String.eqb s "S5,S7")) then Exec_XCHG    ( Z2Z2IBS  4 5   4 7 ) else
if (orb (String.eqb s "s6,s7") (String.eqb s "S6,S7")) then Exec_XCHG    ( Z2Z2IBS  4 6   4 7 ) else
if (orb (String.eqb s "s7,s7") (String.eqb s "S7,S7")) then Exec_XCHG    ( Z2Z2IBS  4 7   4 7 ) else
if (orb (String.eqb s "s8,s7") (String.eqb s "S8,S7")) then Exec_XCHG    ( Z2Z2IBS  4 8   4 7 ) else
if (orb (String.eqb s "s9,s7") (String.eqb s "S9,S7")) then Exec_XCHG    ( Z2Z2IBS  4 9   4 7 ) else
if (orb (String.eqb s "s10,s7") (String.eqb s "S10,S7")) then Exec_XCHG    ( Z2Z2IBS  4 10   4 7 ) else
if (orb (String.eqb s "s11,s7") (String.eqb s "S11,S7")) then Exec_XCHG    ( Z2Z2IBS  4 11   4 7 ) else
if (orb (String.eqb s "s12,s7") (String.eqb s "S12,S7")) then Exec_XCHG    ( Z2Z2IBS  4 12   4 7 ) else
if (orb (String.eqb s "s13,s7") (String.eqb s "S13,S7")) then Exec_XCHG    ( Z2Z2IBS  4 13   4 7 ) else
if (orb (String.eqb s "s14,s7") (String.eqb s "S14,S7")) then Exec_XCHG    ( Z2Z2IBS  4 14   4 7 ) else
if (orb (String.eqb s "s15,s7") (String.eqb s "S15,S7")) then Exec_XCHG    ( Z2Z2IBS  4 15   4 7 ) else

if (orb (String.eqb s "s0,s8") (String.eqb s "S0,S8")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 8 ) else
if (orb (String.eqb s "s1,s8") (String.eqb s "S1,S8")) then Exec_XCHG    ( Z2Z2IBS  4 1   4 8 ) else
if (orb (String.eqb s "s2,s8") (String.eqb s "S2,S8")) then Exec_XCHG    ( Z2Z2IBS  4 2   4 8 ) else
if (orb (String.eqb s "s3,s8") (String.eqb s "S3,S8")) then Exec_XCHG    ( Z2Z2IBS  4 3   4 8 ) else
if (orb (String.eqb s "s4,s8") (String.eqb s "S4,S8")) then Exec_XCHG    ( Z2Z2IBS  4 4   4 8 ) else
if (orb (String.eqb s "s5,s8") (String.eqb s "S5,S8")) then Exec_XCHG    ( Z2Z2IBS  4 5   4 8 ) else
if (orb (String.eqb s "s6,s8") (String.eqb s "S6,S8")) then Exec_XCHG    ( Z2Z2IBS  4 6   4 8 ) else
if (orb (String.eqb s "s7,s8") (String.eqb s "S7,S8")) then Exec_XCHG    ( Z2Z2IBS  4 7   4 8 ) else
if (orb (String.eqb s "s8,s8") (String.eqb s "S8,S8")) then Exec_XCHG    ( Z2Z2IBS  4 8   4 8 ) else
if (orb (String.eqb s "s9,s8") (String.eqb s "S9,S8")) then Exec_XCHG    ( Z2Z2IBS  4 9   4 8 ) else
if (orb (String.eqb s "s10,s8") (String.eqb s "S10,S8")) then Exec_XCHG    ( Z2Z2IBS  4 10   4 8 ) else
if (orb (String.eqb s "s11,s8") (String.eqb s "S11,S8")) then Exec_XCHG    ( Z2Z2IBS  4 11   4 8 ) else
if (orb (String.eqb s "s12,s8") (String.eqb s "S12,S8")) then Exec_XCHG    ( Z2Z2IBS  4 12   4 8 ) else
if (orb (String.eqb s "s13,s8") (String.eqb s "S13,S8")) then Exec_XCHG    ( Z2Z2IBS  4 13   4 8 ) else
if (orb (String.eqb s "s14,s8") (String.eqb s "S14,S8")) then Exec_XCHG    ( Z2Z2IBS  4 14   4 8 ) else
if (orb (String.eqb s "s15,s8") (String.eqb s "S15,S8")) then Exec_XCHG    ( Z2Z2IBS  4 15   4 8 ) else

if (orb (String.eqb s "s0,s9") (String.eqb s "S0,S9")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 9 ) else
if (orb (String.eqb s "s1,s9") (String.eqb s "S1,S9")) then Exec_XCHG    ( Z2Z2IBS  4 1   4 9 ) else
if (orb (String.eqb s "s2,s9") (String.eqb s "S2,S9")) then Exec_XCHG    ( Z2Z2IBS  4 2   4 9 ) else
if (orb (String.eqb s "s3,s9") (String.eqb s "S3,S9")) then Exec_XCHG    ( Z2Z2IBS  4 3   4 9 ) else
if (orb (String.eqb s "s4,s9") (String.eqb s "S4,S9")) then Exec_XCHG    ( Z2Z2IBS  4 4   4 9 ) else
if (orb (String.eqb s "s5,s9") (String.eqb s "S5,S9")) then Exec_XCHG    ( Z2Z2IBS  4 5   4 9 ) else
if (orb (String.eqb s "s6,s9") (String.eqb s "S6,S9")) then Exec_XCHG    ( Z2Z2IBS  4 6   4 9 ) else
if (orb (String.eqb s "s7,s9") (String.eqb s "S7,S9")) then Exec_XCHG    ( Z2Z2IBS  4 7   4 9 ) else
if (orb (String.eqb s "s8,s9") (String.eqb s "S8,S9")) then Exec_XCHG    ( Z2Z2IBS  4 8   4 9 ) else
if (orb (String.eqb s "s9,s9") (String.eqb s "S9,S9")) then Exec_XCHG    ( Z2Z2IBS  4 9   4 9 ) else
if (orb (String.eqb s "s10,s9") (String.eqb s "S10,S9")) then Exec_XCHG    ( Z2Z2IBS  4 10   4 9 ) else
if (orb (String.eqb s "s11,s9") (String.eqb s "S11,S9")) then Exec_XCHG    ( Z2Z2IBS  4 11   4 9 ) else
if (orb (String.eqb s "s12,s9") (String.eqb s "S12,S9")) then Exec_XCHG    ( Z2Z2IBS  4 12   4 9 ) else
if (orb (String.eqb s "s13,s9") (String.eqb s "S13,S9")) then Exec_XCHG    ( Z2Z2IBS  4 13   4 9 ) else
if (orb (String.eqb s "s14,s9") (String.eqb s "S14,S9")) then Exec_XCHG    ( Z2Z2IBS  4 14   4 9 ) else
if (orb (String.eqb s "s15,s9") (String.eqb s "S15,S9")) then Exec_XCHG    ( Z2Z2IBS  4 15   4 9 ) else

if (orb (String.eqb s "s0,s10") (String.eqb s "S0,S10")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 10 ) else
if (orb (String.eqb s "s1,s10") (String.eqb s "S1,S10")) then Exec_XCHG    ( Z2Z2IBS  4 1   4 10 ) else
if (orb (String.eqb s "s2,s10") (String.eqb s "S2,S10")) then Exec_XCHG    ( Z2Z2IBS  4 2   4 10 ) else
if (orb (String.eqb s "s3,s10") (String.eqb s "S3,S10")) then Exec_XCHG    ( Z2Z2IBS  4 3   4 10 ) else
if (orb (String.eqb s "s4,s10") (String.eqb s "S4,S10")) then Exec_XCHG    ( Z2Z2IBS  4 4   4 10 ) else
if (orb (String.eqb s "s5,s10") (String.eqb s "S5,S10")) then Exec_XCHG    ( Z2Z2IBS  4 5   4 10 ) else
if (orb (String.eqb s "s6,s10") (String.eqb s "S6,S10")) then Exec_XCHG    ( Z2Z2IBS  4 6   4 10 ) else
if (orb (String.eqb s "s7,s10") (String.eqb s "S7,S10")) then Exec_XCHG    ( Z2Z2IBS  4 7   4 10 ) else
if (orb (String.eqb s "s8,s10") (String.eqb s "S8,S10")) then Exec_XCHG    ( Z2Z2IBS  4 8   4 10 ) else
if (orb (String.eqb s "s9,s10") (String.eqb s "S9,S10")) then Exec_XCHG    ( Z2Z2IBS  4 9   4 10 ) else
if (orb (String.eqb s "s10,s10") (String.eqb s "S10,S10")) then Exec_XCHG    ( Z2Z2IBS  4 10   4 10 ) else
if (orb (String.eqb s "s11,s10") (String.eqb s "S11,S10")) then Exec_XCHG    ( Z2Z2IBS  4 11   4 10 ) else
if (orb (String.eqb s "s12,s10") (String.eqb s "S12,S10")) then Exec_XCHG    ( Z2Z2IBS  4 12   4 10 ) else
if (orb (String.eqb s "s13,s10") (String.eqb s "S13,S10")) then Exec_XCHG    ( Z2Z2IBS  4 13   4 10 ) else
if (orb (String.eqb s "s14,s10") (String.eqb s "S14,S10")) then Exec_XCHG    ( Z2Z2IBS  4 14   4 10 ) else
if (orb (String.eqb s "s15,s10") (String.eqb s "S15,S10")) then Exec_XCHG    ( Z2Z2IBS  4 15   4 10 ) else

if (orb (String.eqb s "s0,s11") (String.eqb s "S0,S11")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 11 ) else
if (orb (String.eqb s "s1,s11") (String.eqb s "S1,S11")) then Exec_XCHG    ( Z2Z2IBS  4 1   4 11 ) else
if (orb (String.eqb s "s2,s11") (String.eqb s "S2,S11")) then Exec_XCHG    ( Z2Z2IBS  4 2   4 11 ) else
if (orb (String.eqb s "s3,s11") (String.eqb s "S3,S11")) then Exec_XCHG    ( Z2Z2IBS  4 3   4 11 ) else
if (orb (String.eqb s "s4,s11") (String.eqb s "S4,S11")) then Exec_XCHG    ( Z2Z2IBS  4 4   4 11 ) else
if (orb (String.eqb s "s5,s11") (String.eqb s "S5,S11")) then Exec_XCHG    ( Z2Z2IBS  4 5   4 11 ) else
if (orb (String.eqb s "s6,s11") (String.eqb s "S6,S11")) then Exec_XCHG    ( Z2Z2IBS  4 6   4 11 ) else
if (orb (String.eqb s "s7,s11") (String.eqb s "S7,S11")) then Exec_XCHG    ( Z2Z2IBS  4 7   4 11 ) else
if (orb (String.eqb s "s8,s11") (String.eqb s "S8,S11")) then Exec_XCHG    ( Z2Z2IBS  4 8   4 11 ) else
if (orb (String.eqb s "s9,s11") (String.eqb s "S9,S11")) then Exec_XCHG    ( Z2Z2IBS  4 9   4 11 ) else
if (orb (String.eqb s "s10,s11") (String.eqb s "S10,S11")) then Exec_XCHG    ( Z2Z2IBS  4 10   4 11 ) else
if (orb (String.eqb s "s11,s11") (String.eqb s "S11,S11")) then Exec_XCHG    ( Z2Z2IBS  4 11   4 11 ) else
if (orb (String.eqb s "s12,s11") (String.eqb s "S12,S11")) then Exec_XCHG    ( Z2Z2IBS  4 12   4 11 ) else
if (orb (String.eqb s "s13,s11") (String.eqb s "S13,S11")) then Exec_XCHG    ( Z2Z2IBS  4 13   4 11 ) else
if (orb (String.eqb s "s14,s11") (String.eqb s "S14,S11")) then Exec_XCHG    ( Z2Z2IBS  4 14   4 11 ) else
if (orb (String.eqb s "s15,s11") (String.eqb s "S15,S11")) then Exec_XCHG    ( Z2Z2IBS  4 15   4 11 ) else

if (orb (String.eqb s "s0,s12") (String.eqb s "S0,S12")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 12 ) else
if (orb (String.eqb s "s1,s12") (String.eqb s "S1,S12")) then Exec_XCHG    ( Z2Z2IBS  4 1   4 12 ) else
if (orb (String.eqb s "s2,s12") (String.eqb s "S2,S12")) then Exec_XCHG    ( Z2Z2IBS  4 2   4 12 ) else
if (orb (String.eqb s "s3,s12") (String.eqb s "S3,S12")) then Exec_XCHG    ( Z2Z2IBS  4 3   4 12 ) else
if (orb (String.eqb s "s4,s12") (String.eqb s "S4,S12")) then Exec_XCHG    ( Z2Z2IBS  4 4   4 12 ) else
if (orb (String.eqb s "s5,s12") (String.eqb s "S5,S12")) then Exec_XCHG    ( Z2Z2IBS  4 5   4 12 ) else
if (orb (String.eqb s "s6,s12") (String.eqb s "S6,S12")) then Exec_XCHG    ( Z2Z2IBS  4 6   4 12 ) else
if (orb (String.eqb s "s7,s12") (String.eqb s "S7,S12")) then Exec_XCHG    ( Z2Z2IBS  4 7   4 12 ) else
if (orb (String.eqb s "s8,s12") (String.eqb s "S8,S12")) then Exec_XCHG    ( Z2Z2IBS  4 8   4 12 ) else
if (orb (String.eqb s "s9,s12") (String.eqb s "S9,S12")) then Exec_XCHG    ( Z2Z2IBS  4 9   4 12 ) else
if (orb (String.eqb s "s10,s12") (String.eqb s "S10,S12")) then Exec_XCHG    ( Z2Z2IBS  4 10   4 12 ) else
if (orb (String.eqb s "s11,s12") (String.eqb s "S11,S12")) then Exec_XCHG    ( Z2Z2IBS  4 11   4 12 ) else
if (orb (String.eqb s "s12,s12") (String.eqb s "S12,S12")) then Exec_XCHG    ( Z2Z2IBS  4 12   4 12 ) else
if (orb (String.eqb s "s13,s12") (String.eqb s "S13,S12")) then Exec_XCHG    ( Z2Z2IBS  4 13   4 12 ) else
if (orb (String.eqb s "s14,s12") (String.eqb s "S14,S12")) then Exec_XCHG    ( Z2Z2IBS  4 14   4 12 ) else
if (orb (String.eqb s "s15,s12") (String.eqb s "S15,S12")) then Exec_XCHG    ( Z2Z2IBS  4 15   4 12 ) else

if (orb (String.eqb s "s0,s13") (String.eqb s "S0,S13")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 13 ) else
if (orb (String.eqb s "s1,s13") (String.eqb s "S1,S13")) then Exec_XCHG    ( Z2Z2IBS  4 1   4 13 ) else
if (orb (String.eqb s "s2,s13") (String.eqb s "S2,S13")) then Exec_XCHG    ( Z2Z2IBS  4 2   4 13 ) else
if (orb (String.eqb s "s3,s13") (String.eqb s "S3,S13")) then Exec_XCHG    ( Z2Z2IBS  4 3   4 13 ) else
if (orb (String.eqb s "s4,s13") (String.eqb s "S4,S13")) then Exec_XCHG    ( Z2Z2IBS  4 4   4 13 ) else
if (orb (String.eqb s "s5,s13") (String.eqb s "S5,S13")) then Exec_XCHG    ( Z2Z2IBS  4 5   4 13 ) else
if (orb (String.eqb s "s6,s13") (String.eqb s "S6,S13")) then Exec_XCHG    ( Z2Z2IBS  4 6   4 13 ) else
if (orb (String.eqb s "s7,s13") (String.eqb s "S7,S13")) then Exec_XCHG    ( Z2Z2IBS  4 7   4 13 ) else
if (orb (String.eqb s "s8,s13") (String.eqb s "S8,S13")) then Exec_XCHG    ( Z2Z2IBS  4 8   4 13 ) else
if (orb (String.eqb s "s9,s13") (String.eqb s "S9,S13")) then Exec_XCHG    ( Z2Z2IBS  4 9   4 13 ) else
if (orb (String.eqb s "s10,s13") (String.eqb s "S10,S13")) then Exec_XCHG    ( Z2Z2IBS  4 10   4 13 ) else
if (orb (String.eqb s "s11,s13") (String.eqb s "S11,S13")) then Exec_XCHG    ( Z2Z2IBS  4 11   4 13 ) else
if (orb (String.eqb s "s12,s13") (String.eqb s "S12,S13")) then Exec_XCHG    ( Z2Z2IBS  4 12   4 13 ) else
if (orb (String.eqb s "s13,s13") (String.eqb s "S13,S13")) then Exec_XCHG    ( Z2Z2IBS  4 13   4 13 ) else
if (orb (String.eqb s "s14,s13") (String.eqb s "S14,S13")) then Exec_XCHG    ( Z2Z2IBS  4 14   4 13 ) else
if (orb (String.eqb s "s15,s13") (String.eqb s "S15,S13")) then Exec_XCHG    ( Z2Z2IBS  4 15   4 13 ) else

if (orb (String.eqb s "s0,s14") (String.eqb s "S0,S14")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 14 ) else
if (orb (String.eqb s "s1,s14") (String.eqb s "S1,S14")) then Exec_XCHG    ( Z2Z2IBS  4 1   4 14 ) else
if (orb (String.eqb s "s2,s14") (String.eqb s "S2,S14")) then Exec_XCHG    ( Z2Z2IBS  4 2   4 14 ) else
if (orb (String.eqb s "s3,s14") (String.eqb s "S3,S14")) then Exec_XCHG    ( Z2Z2IBS  4 3   4 14 ) else
if (orb (String.eqb s "s4,s14") (String.eqb s "S4,S14")) then Exec_XCHG    ( Z2Z2IBS  4 4   4 14 ) else
if (orb (String.eqb s "s5,s14") (String.eqb s "S5,S14")) then Exec_XCHG    ( Z2Z2IBS  4 5   4 14 ) else
if (orb (String.eqb s "s6,s14") (String.eqb s "S6,S14")) then Exec_XCHG    ( Z2Z2IBS  4 6   4 14 ) else
if (orb (String.eqb s "s7,s14") (String.eqb s "S7,S14")) then Exec_XCHG    ( Z2Z2IBS  4 7   4 14 ) else
if (orb (String.eqb s "s8,s14") (String.eqb s "S8,S14")) then Exec_XCHG    ( Z2Z2IBS  4 8   4 14 ) else
if (orb (String.eqb s "s9,s14") (String.eqb s "S9,S14")) then Exec_XCHG    ( Z2Z2IBS  4 9   4 14 ) else
if (orb (String.eqb s "s10,s14") (String.eqb s "S10,S14")) then Exec_XCHG    ( Z2Z2IBS  4 10   4 14 ) else
if (orb (String.eqb s "s11,s14") (String.eqb s "S11,S14")) then Exec_XCHG    ( Z2Z2IBS  4 11   4 14 ) else
if (orb (String.eqb s "s12,s14") (String.eqb s "S12,S14")) then Exec_XCHG    ( Z2Z2IBS  4 12   4 14 ) else
if (orb (String.eqb s "s13,s14") (String.eqb s "S13,S14")) then Exec_XCHG    ( Z2Z2IBS  4 13   4 14 ) else
if (orb (String.eqb s "s14,s14") (String.eqb s "S14,S14")) then Exec_XCHG    ( Z2Z2IBS  4 14   4 14 ) else
if (orb (String.eqb s "s15,s14") (String.eqb s "S15,S14")) then Exec_XCHG    ( Z2Z2IBS  4 15   4 14 ) else

if (orb (String.eqb s "s0,s15") (String.eqb s "S0,S15")) then Exec_XCHG    ( Z2Z2IBS  4 0   4 15 ) else
if (orb (String.eqb s "s1,s15") (String.eqb s "S1,S15")) then Exec_XCHG    ( Z2Z2IBS  4 1   4 15 ) else
if (orb (String.eqb s "s2,s15") (String.eqb s "S2,S15")) then Exec_XCHG    ( Z2Z2IBS  4 2   4 15 ) else
if (orb (String.eqb s "s3,s15") (String.eqb s "S3,S15")) then Exec_XCHG    ( Z2Z2IBS  4 3   4 15 ) else
if (orb (String.eqb s "s4,s15") (String.eqb s "S4,S15")) then Exec_XCHG    ( Z2Z2IBS  4 4   4 15 ) else
if (orb (String.eqb s "s5,s15") (String.eqb s "S5,S15")) then Exec_XCHG    ( Z2Z2IBS  4 5   4 15 ) else
if (orb (String.eqb s "s6,s15") (String.eqb s "S6,S15")) then Exec_XCHG    ( Z2Z2IBS  4 6   4 15 ) else
if (orb (String.eqb s "s7,s15") (String.eqb s "S7,S15")) then Exec_XCHG    ( Z2Z2IBS  4 7   4 15 ) else
if (orb (String.eqb s "s8,s15") (String.eqb s "S8,S15")) then Exec_XCHG    ( Z2Z2IBS  4 8   4 15 ) else
if (orb (String.eqb s "s9,s15") (String.eqb s "S9,S15")) then Exec_XCHG    ( Z2Z2IBS  4 9   4 15 ) else
if (orb (String.eqb s "s10,s15") (String.eqb s "S10,S15")) then Exec_XCHG    ( Z2Z2IBS  4 10   4 15 ) else
if (orb (String.eqb s "s11,s15") (String.eqb s "S11,S15")) then Exec_XCHG    ( Z2Z2IBS  4 11   4 15 ) else
if (orb (String.eqb s "s12,s15") (String.eqb s "S12,S15")) then Exec_XCHG    ( Z2Z2IBS  4 12   4 15 ) else
if (orb (String.eqb s "s13,s15") (String.eqb s "S13,S15")) then Exec_XCHG    ( Z2Z2IBS  4 13   4 15 ) else
if (orb (String.eqb s "s14,s15") (String.eqb s "S14,S15")) then Exec_XCHG    ( Z2Z2IBS  4 14   4 15 ) else
if (orb (String.eqb s "s15,s15") (String.eqb s "S15,S15")) then Exec_XCHG    ( Z2Z2IBS  4 15   4 15 ) else

return! I.

(* Check Z.pow.

Compute (Z.pow 2 263).
Compute (Z2IBS 264 (14821387422376473014217086081112052205218558037201992197050570753012880593911808%Z)).

 *)

Definition Exec_PUSHSLICEs (s : string) :=
if (String.eqb s "x8000000000000000000000000000000000000000000000000000000000000000001_")
then Exec_PUSHSLICED0 (Z2IBS 264 (14821387422376473014217086081112052205218558037201992197050570753012880593911808%Z) )
else return! I.

Definition tvmCommands := 
[
 {|name := "SECOND"; tvmCommand := TVMNoArgs Exec_SECOND |};
 {|name := "PUSHINT"; tvmCommand := TVMZ1Args Exec_PUSHINTz |};
 {|name := "ROT"; tvmCommand := TVMNoArgs Exec_ROT |};
 {|name := "DICTUSETB"; tvmCommand := TVMNoArgs Exec_DICTUSETB |};
 {|name := "SETSECOND"; tvmCommand := TVMNoArgs Exec_SETSECOND |};
 {|name := "STU"; tvmCommand := TVMZ1Args Exec_STUz |};
 {|name := "DUP"; tvmCommand := TVMNoArgs Exec_DUP |};
 {|name := "NEWC"; tvmCommand := TVMNoArgs Exec_NEWC |};

 {|name := "ACCEPT";tvmCommand := TVMNoArgs Exec_ACCEPT|};
 {|name := "ADD";tvmCommand := TVMNoArgs Exec_ADD|};
 {|name := "AND";tvmCommand := TVMNoArgs Exec_AND|};
 {|name := "BBITS";tvmCommand := TVMNoArgs Exec_BBITS|};
 {|name := "CTOS";tvmCommand := TVMNoArgs Exec_CTOS|};
 {|name := "DEC";tvmCommand := TVMNoArgs Exec_DEC|};
 {|name := "DICTUDEL";tvmCommand := TVMNoArgs Exec_DICTUDEL|};
 {|name := "DICTUGET";tvmCommand := TVMNoArgs Exec_DICTUGET|};
 {|name := "DICTUMAX";tvmCommand := TVMNoArgs Exec_DICTUMAX|};
 {|name := "DIV";tvmCommand := TVMNoArgs Exec_DIV|};
 {|name := "ENDC";tvmCommand := TVMNoArgs Exec_ENDC|};
 {|name := "ENDS";tvmCommand := TVMNoArgs Exec_ENDS|};
 {|name := "EQINT";tvmCommand := TVMZ1Args Exec_EQINTz|};
 {|name := "EQUAL";tvmCommand := TVMNoArgs Exec_EQUAL|};

 {|name := "EXECUTE";tvmCommand := TVMBS1Args Exec_EXECUTE|};
 {|name := "FIRST";tvmCommand := TVMNoArgs Exec_FIRST|};
 {|name := "GEQ";tvmCommand := TVMNoArgs Exec_GEQ|};
 {|name := "GREATER";tvmCommand := TVMNoArgs Exec_GREATER|};
 {|name := "IFJMP";tvmCommand := TVMNoArgs Exec_IFJMP|};
 {|name := "IFNOT";tvmCommand := TVMNoArgs Exec_IFNOT|};
 {|name := "IFNOTJMP";tvmCommand := TVMBS1Args Exec_IFNOTJMP|};
 {|name := "IFOP";tvmCommand := TVMBS1Args Exec_IFOP|};
 {|name := "INC";tvmCommand := TVMNoArgs Exec_INC|};
 {|name := "ISNULL";tvmCommand := TVMNoArgs Exec_ISNULL|};
 {|name := "JMP";tvmCommand := TVMZ1Args Exec_JMP|};
 {|name := "LDDICT";tvmCommand := TVMNoArgs Exec_LDDICT|};
 {|name := "LDI";tvmCommand := TVMZ1Args Exec_LDIz|};
 {|name := "LDIX";tvmCommand := TVMNoArgs Exec_LDIX|};
 {|name := "LDREF";tvmCommand := TVMNoArgs Exec_LDREF|};
 {|name := "LDSLICEX";tvmCommand := TVMNoArgs Exec_LDSLICEX|};
 {|name := "LDU";tvmCommand := TVMZ1Args Exec_LDUz|};
 {|name := "LDUX";tvmCommand := TVMNoArgs Exec_LDUX|};
 {|name := "LEQ";tvmCommand := TVMNoArgs Exec_LEQ|};
 {|name := "LESS";tvmCommand := TVMNoArgs Exec_LESS|};
 {|name := "LESSINT";tvmCommand := TVMZ1Args Exec_LESSINTz|};
 {|name := "MUL";tvmCommand := TVMNoArgs Exec_MUL|};
 {|name := "OR";tvmCommand := TVMNoArgs Exec_OR|};
 {|name := "POP";tvmCommand := TVMStr1Args Exec_POPs|};
 {|name := "POPCTR";tvmCommand := TVMStr1Args Exec_POPCTRs|};
 
 {|name := "POPROOT";tvmCommand := TVMNoArgs Exec_POPROOT|};
 {|name := "PRINTSTR";tvmCommand := TVMNoArgs Exec_PRINTSTR|};
 {|name := "PUSH";    tvmCommand := TVMStr1Args Exec_PUSHs|};
 {|name := "PUSHCTR";    tvmCommand := TVMStr1Args Exec_PUSHCTRs|};

 {|name := "PUSHCONT"; tvmCommand := TVMCode1Args Exec_PUSHCONT|};

 {|name := "PUSHROOT";tvmCommand := TVMNoArgs Exec_PUSHROOT|};
 {|name := "ROT";tvmCommand := TVMNoArgs Exec_ROT|};
 {|name := "SCHKBITSQ";tvmCommand := TVMNoArgs Exec_SCHKBITSQ|};
 {|name := "SDEMPTY";tvmCommand := TVMNoArgs Exec_SDEMPTY|};
 {|name := "SDEQ";tvmCommand := TVMNoArgs Exec_SDEQ|};
 {|name := "SECOND";tvmCommand := TVMNoArgs Exec_SECOND|};
 {|name := "SEMPTY";tvmCommand := TVMNoArgs Exec_SEMPTY|};
 {|name := "SETCP";tvmCommand := TVMBS1Args Exec_SETCP|};
 {|name := "SETSECOND";tvmCommand := TVMNoArgs Exec_SETSECOND|};
 {|name := "SETTHIRD";tvmCommand := TVMNoArgs Exec_SETTHIRD|};
 {|name := "SREMPTY";tvmCommand := TVMNoArgs Exec_SREMPTY|};
 {|name := "STBR";tvmCommand := TVMNoArgs Exec_STBR|};
 {|name := "STDICT";tvmCommand := TVMNoArgs Exec_STDICT|};
 {|name := "STGRAMS";tvmCommand := TVMNoArgs Exec_STGRAMS|};
 {|name := "STI";tvmCommand := TVMZ1Args Exec_STIz|};
 {|name := "STONES";tvmCommand := TVMNoArgs Exec_STONES|};
 {|name := "STREF";tvmCommand := TVMNoArgs Exec_STREF|};
 {|name := "STREFR";tvmCommand := TVMNoArgs Exec_STREFR|};
 {|name := "STSLICE";tvmCommand := TVMNoArgs Exec_STSLICE|};

 {|name := "STZEROES";tvmCommand := TVMNoArgs Exec_STZEROES|};
 {|name := "SUB";tvmCommand := TVMNoArgs Exec_SUB|};
 {|name := "THIRD";tvmCommand := TVMNoArgs Exec_THIRD|};
 {|name := "THROWANY";tvmCommand := TVMNoArgs Exec_THROWANY|};
 {|name := "THROWIF";tvmCommand := TVMZ1Args Exec_THROWIFz|};
 {|name := "THROWIFNOT";tvmCommand := TVMZ1Args Exec_THROWIFNOTz|};
 {|name := "TPUSH";tvmCommand := TVMNoArgs Exec_TPUSH|};
 {|name := "TUPLE";tvmCommand := TVMBS1Args Exec_TUPLE|};
 {|name := "UFITS";tvmCommand := TVMZ1Args Exec_UFITSz|};
 {|name := "XCHG";tvmCommand := TVMStr1Args Exec_XCHGs|};

 {|name := "BLKDROP";tvmCommand := TVMZ1Args Exec_BLKDROPz |};
 {|name := "BLKSWAP";tvmCommand := TVMZ2Args Exec_BLKSWAPz |};
 {|name := "DICTUGETNEXT";tvmCommand := TVMNoArgs Exec_DICTUGETNEXT |};
 {|name := "DICTUGETREF";tvmCommand := TVMNoArgs Exec_DICTUGETREF |};
 {|name := "DICTUMINREF";tvmCommand := TVMNoArgs Exec_DICTUMINREF |};
 {|name := "DICTUSETREF";tvmCommand := TVMNoArgs Exec_DICTUSETREF |};
 {|name := "DROP";tvmCommand := TVMNoArgs Exec_DROP |};
 {|name := "DROP2";tvmCommand := TVMNoArgs Exec_DROP2 |};
 {|name := "GETPARAM";tvmCommand := TVMBS1Args Exec_GETPARAM |};
 {|name := "GTINT";tvmCommand := TVMBS1Args Exec_GTINT |};
 {|name := "IFELSE";tvmCommand := TVMBS1Args Exec_IFELSE |};
 {|name := "INDEX";tvmCommand := TVMZ1Args Exec_INDEXz |};
 {|name := "LDDICTS";tvmCommand := TVMNoArgs Exec_LDDICTS |};
 {|name := "LDREFRTOS";tvmCommand := TVMNoArgs Exec_LDREFRTOS |};
 {|name := "LDSLICE";tvmCommand := TVMZ1Args Exec_LDSLICEz |};
 {|name := "LSHIFT";tvmCommand := TVMNoArgs Exec_LSHIFT |};
 {|name := "NEQINT";tvmCommand := TVMBS1Args Exec_NEQINT |};
 {|name := "NEWDICT";tvmCommand := TVMNoArgs Exec_NEWDICT |};
 {|name := "PUSHNULL";tvmCommand := TVMNoArgs Exec_PUSHNULL |};
 {|name := "ONLYTOPX";tvmCommand := TVMNoArgs Exec_ONLYTOPX |};
 {|name := "PLDDICT";tvmCommand := TVMNoArgs Exec_PLDDICT |};
 {|name := "PLDI";tvmCommand := TVMBS1Args Exec_PLDI |};
 {|name := "PLDREF";tvmCommand := TVMNoArgs Exec_PLDREF |};
 {|name := "PLDREFIDX";tvmCommand := TVMBS1Args Exec_PLDREFIDX |};
 {|name := "PLDU";tvmCommand := TVMZ1Args Exec_PLDUz |};
 {|name := "PUSH2";tvmCommand := TVMBS1Args Exec_PUSH2 |};
 {|name := "PUSHPOW2DEC";tvmCommand := TVMZ1Args Exec_PUSHPOW2DECz |};
 {|name := "PUSHSLICE";tvmCommand := TVMStr1Args Exec_PUSHSLICEs |};
 {|name := "RET";tvmCommand := TVMNoArgs Exec_RET |};
 {|name := "ROTREV";tvmCommand := TVMNoArgs Exec_ROTREV |};
 {|name := "RSHIFT";tvmCommand := TVMNoArgs Exec_RSHIFT |};
 {|name := "SDSKIPFIRST";tvmCommand := TVMNoArgs Exec_SDSKIPFIRST |};
 {|name := "SKIPDICT";tvmCommand := TVMNoArgs Exec_SKIPDICT |};
 {|name := "SPLIT";tvmCommand := TVMNoArgs Exec_SPLIT |};
 {|name := "SSKIPFIRST";tvmCommand := TVMNoArgs Exec_SSKIPFIRST |};
 {|name := "STBREF";tvmCommand := TVMNoArgs Exec_STBREF |};
 {|name := "STBREFR";tvmCommand := TVMNoArgs Exec_STBREFR |};
 {|name := "STIR";tvmCommand := TVMZ1Args Exec_STIRz |};
 {|name := "STSLICER";tvmCommand := TVMNoArgs Exec_STSLICER |};
 {|name := "STUR";tvmCommand := TVMZ1Args Exec_STURz |};
 {|name := "UNTIL";tvmCommand := TVMNoArgs Exec_UNTIL |};
 {|name := "BLESS";tvmCommand := TVMNoArgs Exec_BLESS |}; 
 {|name := "BREMBITS";tvmCommand := TVMNoArgs Exec_BREMBITS |}; 
 {|name := "CONDSEL";tvmCommand := TVMNoArgs Exec_CONDSEL |}; 
 {|name := "DROPX";tvmCommand := TVMNoArgs Exec_DROPX |}; 
 {|name := "PUSHCONT";tvmCommand := TVMBS1Args Exec_PUSHCONTF80 |}; 
 {|name := "PUSHPOW2DEC";tvmCommand := TVMBS1Args Exec_PUSHPOW2DEC |}; 
 {|name := "PUSHSLICE";tvmCommand := TVMBS1Args Exec_PUSHSLICED0 |}; 
 {|name := "SBITS";tvmCommand := TVMNoArgs Exec_SBITS |}; 
 {|name := "SETINDEX";tvmCommand := TVMBS1Args Exec_SETINDEX |}; 
 {|name := "SREFS";tvmCommand := TVMNoArgs Exec_SREFS |}; 
 {|name := "SUBR";tvmCommand := TVMNoArgs Exec_SUBR |}; 
 {|name := "UNPAIR";tvmCommand := TVMNoArgs Exec_UNPAIR |}; 
 {|name := "DUP";tvmCommand := TVMNoArgs Exec_DUP |}; 
 {|name := "LTIME";tvmCommand := TVMNoArgs Exec_LTIME |}; 
 {|name := "NIP";tvmCommand := TVMNoArgs Exec_NIP |}; 
 {|name := "NOW";tvmCommand := TVMNoArgs Exec_NOW |}; 
 {|name := "SWAP";tvmCommand := TVMNoArgs Exec_SWAP |}; 
 {|name := "SWAP2";tvmCommand := TVMNoArgs Exec_SWAP2 |}; 
 {|name := "FALSE";tvmCommand := TVMNoArgs Exec_FALSE |}; 
 {|name := "TRUE";tvmCommand := TVMNoArgs Exec_TRUE |}; 

 {|name := "CALL";tvmCommand := TVMBS1Args Exec_CALL |}; 
 {|name := "CALLX";tvmCommand := TVMNoArgs Exec_CALLX |}; 
 {|name := "COMMIT";tvmCommand := TVMNoArgs Exec_COMMIT |}; 
 {|name := "DICTUMIN";tvmCommand := TVMNoArgs Exec_DICTUMIN |}; 
 {|name := "HASHCU";tvmCommand := TVMNoArgs Exec_HASHCU |}; 
 {|name := "LDMSGADDR";tvmCommand := TVMNoArgs Exec_LDMSGADDR |}; 
 {|name := "REVERSE";tvmCommand := TVMZ2Args Exec_REVERSEz |}; 
 {|name := "SCUTFIRST";tvmCommand := TVMBS1Args Exec_SCUTFIRST |}; 

 {|name := "CALL";tvmCommand := TVMBS1Args Exec_CALL |};
 {|name := "CALLDICT";tvmCommand := TVMBS1Args Exec_CALLDICT |};
 {|name := "CHKSIGNU";tvmCommand := TVMNoArgs Exec_CHKSIGNU |};
 {|name := "LDMSGADDR";tvmCommand := TVMNoArgs Exec_LDMSGADDR |};
 
 {|name := "PARSEMSGADDR";tvmCommand := TVMNoArgs Exec_PARSEMSGADDR |};
 {|name := "PUSHREFCONT";tvmCommand := TVMNoArgs Exec_PUSHREFCONT |};
 {|name := "SENDRAWMSG";tvmCommand := TVMNoArgs Exec_SENDRAWMSG |};
 {|name := "SETCODE";tvmCommand := TVMNoArgs Exec_SETCODE |};
 {|name := "DEPTH";tvmCommand := TVMNoArgs Exec_DEPTH |};
 {|name := "PICK";tvmCommand := TVMNoArgs Exec_PICK |};
 {|name := "PAIR";tvmCommand := TVMNoArgs Exec_PAIR |};
 {|name := "MYADDR";tvmCommand := TVMNoArgs Exec_MYADDR |}; 

(*  {|name := "";tvmCommand := TVMNoArgs Exec_ |};  *)
 
 {|name := "}"; tvmCommand := TVMEndCont |}
].

Require Import TVMModel.Base.Definitions.TVMHashmapDisplay.
Require Import TVMModel.Base.Definitions.TVMCellHashmap.
Require Import TVMModel.Base.Definitions.TVMHashmap.
Let cell := _TVMOrdinaryCell
                    [>D0, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1,
                    D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1,
                    D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1,
                    D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1,
                    D1, D1, D1, D1, D1, D1, D1, D1, D0, D0, D0, D0, D0, D0,
                    D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0,
                    D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0,
                    D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0,
                    D0, D0, D0, D0, D0, D0, D0, D0, D0, D1, D1, D0, D0, D1,
                    D0, D0, D0, D0, D0, D0, D0, D0, D0, D1, D0, D1 <]
                    _TVMNullCell _TVMNullCell _TVMNullCell _TVMNullCell.

Let defhm := _TVMHashmapLeaf TVMCell TVMBitStringEmpty _TVMNullCell.

Let hashmap := tvmCell2Hashmap cell defhm.

(* Check hashmap.

Compute hashmapCellDisplay hashmap. *)

Require Import Byte.
Require Import TVMModel.Base.Definitions.TVMBitString.

Module BitStringBinaryNotations.


Fixpoint bitString2Bytes (l : TVMBitString) : list Byte.byte := 
match l with 
| TVMBitStringEmpty  => [ ]
| TVMBitStringAdd l' D0 =>  x30 :: (bitString2Bytes l')
| TVMBitStringAdd l' D1 =>  x31 :: (bitString2Bytes l')
end.    

Fixpoint bytes2BitString ( bl : list Byte.byte ) : option TVMBitString :=
match bl with 
| [ ]  => Some TVMBitStringEmpty
| x30 :: bl' => let s' := bytes2BitString bl' in 
             match s' with
             | None => None 
             | Some s'' => Some (TVMBitStringAdd s'' D0)
             end
| x31 :: bl' => let s' := bytes2BitString bl' in 
             match s' with
             | None => None 
             | Some s'' => Some (TVMBitStringAdd s'' D1)
             end
| _ => None
end.

(* Compute ( [> D0, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1,
                    D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1,
                    D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1,
                    D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1, D1,
                    D1, D1, D1, D1, D1, D1, D1, D1, D0, D0, D0, D0, D0, D0,
                    D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0,
                    D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0,
                    D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0, D0,
                    D0, D0, D0, D0, D0, D0, D0, D0, D0, D1, D1, D0, D0, D1,
                    D0, D0, D0, D0, D0, D0, D0, D0, D0, D1, D0, D1 <] ).
 *)
Declare Scope tvm_scope_bin.
Delimit Scope tvm_scope_bin with tvm_bin.
String Notation TVMBitString bytes2BitString bitString2Bytes : tvm_scope_bin.

Local Open Scope tvm_scope_bin.

(*Compute (TVMBitStringAdd TVMBitStringEmpty  D1)%tvm.

Compute ( [> D0, D1, D1, D1, D0, D1, D1, D1, D0, D1, D1, D1 <] )%tvm.*)

Definition bit2nat (i:TVMBit) : nat :=
match i with
| D0 => 0%nat
| D1 => 1%nat
end.

Definition bits2Hex (l : list TVMBit ) : option byte := 
match l with
| [ ] => None
| [q] => Byte.of_nat (bit2nat q)
| [ q ; q' ] => Byte.of_nat ( 2 * (bit2nat q') + (bit2nat q) )
| [ q ; q' ; q'' ] => Byte.of_nat ( 4 * (bit2nat q'') + 2 * (bit2nat q') + (bit2nat q) )
| [ q ; q' ; q'' ; q''' ] => Byte.of_nat ( 8 * (bit2nat q''') + 4 * (bit2nat q'') + 2 * (bit2nat q') + (bit2nat q) )
| _ => None
end.

(* Print Byte.byte. *)

Definition toHex (b:Byte.byte) :=
match b with
| x00 => x30
| x01 => x31 
| x02 => x32
| x03 => x33 
| x04 => x34
| x05 => x35 
| x06 => x36
| x07 => x37 
| x08 => x38
| x09 => x39 
| x0a => x41
| x0b => x42 
| x0c => x43
| x0d => x44 
| x0e => x45
| x0f => x46
| _ => x00
end.

Definition toBytes (b:Byte.byte) :=
match b with
| x30 => x00
| x31 => x01
| x32 => x02
| x33 => x03
| x34 => x04
| x35 => x05
| x36 => x06
| x37 => x07
| x38 => x08
| x39 => x09
| x41 => x0a
| x42 => x0b
| x43 => x0c
| x44 => x0d
| x45 => x0e
| x46 => x0f
| _ => x00
end.

(* Compute (toBytes (toHex x0f%byte)).  *)

Fixpoint bitString2Hex' (acc : list TVMBit) (l : TVMBitString) : list Byte.byte := 
match l with 
| TVMBitStringEmpty  => match (bits2Hex acc) with
                        | None => [ ] 
                        | Some x => [ (toHex x) ]
                        end
| TVMBitStringAdd l' bit =>  if (Nat.leb (List.length acc) 2)  then bitString2Hex' ( bit :: acc ) l'
                                                          else match bits2Hex ( bit :: acc ) with
                                                               | None => (bitString2Hex' [ ] l')
                                                               | Some y => (toHex y) :: (bitString2Hex' [ ] l')
                                                               end
end.    

Definition bitString2Hex := bitString2Hex' [ ].

(* Check bitString2Hex.

Compute (bitString2Hex [> D1, D1, D0, D1 <]).

Print TVMBitString.

Print list. *)
  
Fixpoint hex2BitString ( bl : list Byte.byte ) :=
match bl with 
| [ ]    => TVMBitStringEmpty
| h :: t => match h with
            | x30 => TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (hex2BitString t) D0 ) D0 ) D0 ) D0 
            | x31 => TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (hex2BitString t) D1 ) D0 ) D0 ) D0 
            | x32 => TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (hex2BitString t) D0 ) D1 ) D0 ) D0 
            | x33 => TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (hex2BitString t) D1 ) D1 ) D0 ) D0 
            | x34 => TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (hex2BitString t) D0 ) D0 ) D1 ) D0 
            | x35 => TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (hex2BitString t) D1 ) D0 ) D1 ) D0 
            | x36 => TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (hex2BitString t) D0 ) D1 ) D1 ) D0 
            | x37 => TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (hex2BitString t) D1 ) D1 ) D1 ) D0 
            | x38 => TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (hex2BitString t) D0 ) D0 ) D0 ) D1 
            | x39 => TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (hex2BitString t) D1 ) D0 ) D0 ) D1 
            | x41 => TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (hex2BitString t) D0 ) D1 ) D0 ) D1 
            | x42 => TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (hex2BitString t) D1 ) D1 ) D0 ) D1
            | x43 => TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (hex2BitString t) D0 ) D0 ) D1 ) D1 
            | x44 => TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (hex2BitString t) D1 ) D0 ) D1 ) D1 
            | x45 => TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (hex2BitString t) D0 ) D1 ) D1 ) D1 
            | x46 => TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (TVMBitStringAdd (hex2BitString t) D1 ) D1 ) D1 ) D1 
            | _ => TVMBitStringEmpty
            end
end.

End BitStringBinaryNotations.

(* Compute (hex2BitString (x30::x31::x32::x33::x34::x35::x36::x37::x38::x39::x41::x42::x44::x45::x46::[ ])).
 *)

(*Declare Scope tvm_scope.
Delimit Scope tvm_scope with tvm.
String Notation TVMBitString hex2BitString bitString2Hex : tvm_scope.*)

(* Compute (hex2BitString (x30::x31::x32::x33::x34::x35::x36::x37::x38::x39::x41::x42::x44::x45::x46::[ ])).
 *)



