Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import FinProof.ProgrammingWith.

Local Open Scope record.
Local Open Scope program_scope. 

Require Import FinProof.Common.
Require Import FinProof.StateMonad2.
Require Import depoolContract.SolidityNotations.

Notation "·0"  := (Here)       (at level 60, right associativity). 
 Notation "·1":= (Next (·0))  (at level 60, right associativity). 
 Notation "·2":= (Next (·1))  (at level 60, right associativity). 
 Notation "·3":= (Next (·2))  (at level 60, right associativity). 
 Notation "·4":= (Next (·3))  (at level 60, right associativity). 
 Notation "·5":= (Next (·4))  (at level 60, right associativity). 
 Notation "·6":= (Next (·5))  (at level 60, right associativity). 
 Notation "·7":= (Next (·6))  (at level 60, right associativity). 
 Notation "·8":= (Next (·7))  (at level 60, right associativity). 
 Notation "·9":= (Next (·8))  (at level 60, right associativity). 
 Notation "·10":= (Next (·9))  (at level 60, right associativity). 
 Notation "·11":= (Next (·10))  (at level 60, right associativity). 
 Notation "·12":= (Next (·11))  (at level 60, right associativity). 
 Notation "·13":= (Next (·12))  (at level 60, right associativity). 
 Notation "·14":= (Next (·13))  (at level 60, right associativity). 
 Notation "·15":= (Next (·14))  (at level 60, right associativity). 
 Notation "·16":= (Next (·15))  (at level 60, right associativity). 
 Notation "·17":= (Next (·16))  (at level 60, right associativity). 
 Notation "·18":= (Next (·17))  (at level 60, right associativity). 
 Notation "·19":= (Next (·18))  (at level 60, right associativity). 
 Notation "·20":= (Next (·19))  (at level 60, right associativity). 
 Notation "·21":= (Next (·20))  (at level 60, right associativity). 
 Notation "·22":= (Next (·21))  (at level 60, right associativity). 
 Notation "·23":= (Next (·22))  (at level 60, right associativity). 
 Notation "·24":= (Next (·23))  (at level 60, right associativity). 
 Notation "·25":= (Next (·24))  (at level 60, right associativity). 
 Notation "·26":= (Next (·25))  (at level 60, right associativity). 
 Notation "·27":= (Next (·26))  (at level 60, right associativity). 
 Notation "·28":= (Next (·27))  (at level 60, right associativity). 
 Notation "·29":= (Next (·28))  (at level 60, right associativity). 
 Notation "·30":= (Next (·29))  (at level 60, right associativity). 
 Notation "·31":= (Next (·30))  (at level 60, right associativity). 
 Notation "·32":= (Next (·31))  (at level 60, right associativity). 
 Notation "·33":= (Next (·32))  (at level 60, right associativity). 
 Notation "·34":= (Next (·33))  (at level 60, right associativity). 
 Notation "·35":= (Next (·34))  (at level 60, right associativity). 
 Notation "·36":= (Next (·35))  (at level 60, right associativity). 
 Notation "·37":= (Next (·36))  (at level 60, right associativity). 
 Notation "·38":= (Next (·37))  (at level 60, right associativity). 
 Notation "·39":= (Next (·38))  (at level 60, right associativity). 
 Notation "·40":= (Next (·39))  (at level 60, right associativity). 
 Notation "·41":= (Next (·40))  (at level 60, right associativity). 
 Notation "·42":= (Next (·41))  (at level 60, right associativity). 
 Notation "·43":= (Next (·42))  (at level 60, right associativity). 
 Notation "·44":= (Next (·43))  (at level 60, right associativity). 
 Notation "·45":= (Next (·44))  (at level 60, right associativity). 
 Notation "·46":= (Next (·45))  (at level 60, right associativity). 
 Notation "·47":= (Next (·46))  (at level 60, right associativity). 
 Notation "·48":= (Next (·47))  (at level 60, right associativity). 
 Notation "·49":= (Next (·48))  (at level 60, right associativity). 
 Notation "·50":= (Next (·49))  (at level 60, right associativity). 
 Notation "·51":= (Next (·50))  (at level 60, right associativity). 
 Notation "·52":= (Next (·51))  (at level 60, right associativity). 
 Notation "·53":= (Next (·52))  (at level 60, right associativity). 
 Notation "·54":= (Next (·53))  (at level 60, right associativity). 
 Notation "·55":= (Next (·54))  (at level 60, right associativity). 
 Notation "·56":= (Next (·55))  (at level 60, right associativity). 
 Notation "·57":= (Next (·56))  (at level 60, right associativity). 
 Notation "·58":= (Next (·57))  (at level 60, right associativity). 
 Notation "·59":= (Next (·58))  (at level 60, right associativity). 
 Notation "·60":= (Next (·59))  (at level 60, right associativity). 
 Notation "·61":= (Next (·60))  (at level 60, right associativity). 
 Notation "·62":= (Next (·61))  (at level 60, right associativity). 
 Notation "·63":= (Next (·62))  (at level 60, right associativity). 
 Notation "·64":= (Next (·63))  (at level 60, right associativity). 
 Notation "·65":= (Next (·64))  (at level 60, right associativity). 
 Notation "·66":= (Next (·65))  (at level 60, right associativity). 
 Notation "·67":= (Next (·66))  (at level 60, right associativity). 
 Notation "·68":= (Next (·67))  (at level 60, right associativity). 
 Notation "·69":= (Next (·68))  (at level 60, right associativity). 
 Notation "·70":= (Next (·69))  (at level 60, right associativity). 
 Notation "·71":= (Next (·70))  (at level 60, right associativity). 
 Notation "·72":= (Next (·71))  (at level 60, right associativity). 
 Notation "·73":= (Next (·72))  (at level 60, right associativity). 
 Notation "·74":= (Next (·73))  (at level 60, right associativity). 
 Notation "·75":= (Next (·74))  (at level 60, right associativity). 
 Notation "·76":= (Next (·75))  (at level 60, right associativity). 
 Notation "·77":= (Next (·76))  (at level 60, right associativity). 
 Notation "·78":= (Next (·77))  (at level 60, right associativity). 
 Notation "·79":= (Next (·78))  (at level 60, right associativity). 
 Notation "·80":= (Next (·79))  (at level 60, right associativity). 
 Notation "·81":= (Next (·80))  (at level 60, right associativity). 
 Notation "·82":= (Next (·81))  (at level 60, right associativity). 
 Notation "·83":= (Next (·82))  (at level 60, right associativity). 
 Notation "·84":= (Next (·83))  (at level 60, right associativity). 
 Notation "·85":= (Next (·84))  (at level 60, right associativity). 
 Notation "·86":= (Next (·85))  (at level 60, right associativity). 
 Notation "·87":= (Next (·86))  (at level 60, right associativity). 
 Notation "·88":= (Next (·87))  (at level 60, right associativity). 
 Notation "·89":= (Next (·88))  (at level 60, right associativity). 
 Notation "·90":= (Next (·89))  (at level 60, right associativity). 
 Notation "·91":= (Next (·90))  (at level 60, right associativity). 
 Notation "·92":= (Next (·91))  (at level 60, right associativity). 
 Notation "·93":= (Next (·92))  (at level 60, right associativity). 
 Notation "·94":= (Next (·93))  (at level 60, right associativity). 
 Notation "·95":= (Next (·94))  (at level 60, right associativity). 
 Notation "·96":= (Next (·95))  (at level 60, right associativity). 
 Notation "·97":= (Next (·96))  (at level 60, right associativity). 
 Notation "·98":= (Next (·97))  (at level 60, right associativity). 
 Notation "·99":= (Next (·98))  (at level 60, right associativity). 
 Notation "·100":= (Next (·99))  (at level 60, right associativity). 
 Notation "·101":= (Next (·100))  (at level 60, right associativity). 
 Notation "·102":= (Next (·101))  (at level 60, right associativity). 
 Notation "·103":= (Next (·102))  (at level 60, right associativity). 
 Notation "·104":= (Next (·103))  (at level 60, right associativity). 
 Notation "·105":= (Next (·104))  (at level 60, right associativity). 
 Notation "·106":= (Next (·105))  (at level 60, right associativity). 
 Notation "·107":= (Next (·106))  (at level 60, right associativity). 
 Notation "·108":= (Next (·107))  (at level 60, right associativity). 
 Notation "·109":= (Next (·108))  (at level 60, right associativity). 
 Notation "·110":= (Next (·109))  (at level 60, right associativity). 
 Notation "·111":= (Next (·110))  (at level 60, right associativity). 
 Notation "·112":= (Next (·111))  (at level 60, right associativity). 
 Notation "·113":= (Next (·112))  (at level 60, right associativity). 
 Notation "·114":= (Next (·113))  (at level 60, right associativity). 
 Notation "·115":= (Next (·114))  (at level 60, right associativity). 
 Notation "·116":= (Next (·115))  (at level 60, right associativity). 
 Notation "·117":= (Next (·116))  (at level 60, right associativity). 
 Notation "·118":= (Next (·117))  (at level 60, right associativity). 
 Notation "·119":= (Next (·118))  (at level 60, right associativity). 
 Notation "·120":= (Next (·119))  (at level 60, right associativity). 
 Notation "·121":= (Next (·120))  (at level 60, right associativity). 
 Notation "·122":= (Next (·121))  (at level 60, right associativity). 
 Notation "·123":= (Next (·122))  (at level 60, right associativity). 
 Notation "·124":= (Next (·123))  (at level 60, right associativity). 
 Notation "·125":= (Next (·124))  (at level 60, right associativity). 
 Notation "·126":= (Next (·125))  (at level 60, right associativity). 
 Notation "·127":= (Next (·126))  (at level 60, right associativity). 
 Notation "·128":= (Next (·127))  (at level 60, right associativity). 
 Notation "·129":= (Next (·128))  (at level 60, right associativity). 
 Notation "·130":= (Next (·129))  (at level 60, right associativity). 
 Notation "·131":= (Next (·130))  (at level 60, right associativity). 
 Notation "·132":= (Next (·131))  (at level 60, right associativity). 
 Notation "·133":= (Next (·132))  (at level 60, right associativity). 
 Notation "·134":= (Next (·133))  (at level 60, right associativity). 
 Notation "·135":= (Next (·134))  (at level 60, right associativity). 
 Notation "·136":= (Next (·135))  (at level 60, right associativity). 
 Notation "·137":= (Next (·136))  (at level 60, right associativity). 
 Notation "·138":= (Next (·137))  (at level 60, right associativity). 
 Notation "·139":= (Next (·138))  (at level 60, right associativity). 
 Notation "·140":= (Next (·139))  (at level 60, right associativity). 
 Notation "·141":= (Next (·140))  (at level 60, right associativity). 
 Notation "·142":= (Next (·141))  (at level 60, right associativity). 
 Notation "·143":= (Next (·142))  (at level 60, right associativity). 
 Notation "·144":= (Next (·143))  (at level 60, right associativity). 
 Notation "·145":= (Next (·144))  (at level 60, right associativity). 
 Notation "·146":= (Next (·145))  (at level 60, right associativity). 
 Notation "·147":= (Next (·146))  (at level 60, right associativity). 
 Notation "·148":= (Next (·147))  (at level 60, right associativity). 
 Notation "·149":= (Next (·148))  (at level 60, right associativity). 
 Notation "·150":= (Next (·149))  (at level 60, right associativity). 
 Notation "·151":= (Next (·150))  (at level 60, right associativity). 
 Notation "·152":= (Next (·151))  (at level 60, right associativity). 
 Notation "·153":= (Next (·152))  (at level 60, right associativity). 
 Notation "·154":= (Next (·153))  (at level 60, right associativity). 
 Notation "·155":= (Next (·154))  (at level 60, right associativity). 
 Notation "·156":= (Next (·155))  (at level 60, right associativity). 
 Notation "·157":= (Next (·156))  (at level 60, right associativity). 
 Notation "·158":= (Next (·157))  (at level 60, right associativity). 
 Notation "·159":= (Next (·158))  (at level 60, right associativity). 
 Notation "·160":= (Next (·159))  (at level 60, right associativity). 
 Notation "·161":= (Next (·160))  (at level 60, right associativity). 
 Notation "·162":= (Next (·161))  (at level 60, right associativity). 
 Notation "·163":= (Next (·162))  (at level 60, right associativity). 
 Notation "·164":= (Next (·163))  (at level 60, right associativity). 
 Notation "·165":= (Next (·164))  (at level 60, right associativity). 
 Notation "·166":= (Next (·165))  (at level 60, right associativity). 
 Notation "·167":= (Next (·166))  (at level 60, right associativity). 
 Notation "·168":= (Next (·167))  (at level 60, right associativity). 
 Notation "·169":= (Next (·168))  (at level 60, right associativity). 
 Notation "·170":= (Next (·169))  (at level 60, right associativity). 
 Notation "·171":= (Next (·170))  (at level 60, right associativity). 
 Notation "·172":= (Next (·171))  (at level 60, right associativity). 
 Notation "·173":= (Next (·172))  (at level 60, right associativity). 
 Notation "·174":= (Next (·173))  (at level 60, right associativity). 
 Notation "·175":= (Next (·174))  (at level 60, right associativity). 
 Notation "·176":= (Next (·175))  (at level 60, right associativity). 
 Notation "·177":= (Next (·176))  (at level 60, right associativity). 
 Notation "·178":= (Next (·177))  (at level 60, right associativity). 
 Notation "·179":= (Next (·178))  (at level 60, right associativity). 
 Notation "·180":= (Next (·179))  (at level 60, right associativity). 
 Notation "·181":= (Next (·180))  (at level 60, right associativity). 
 Notation "·182":= (Next (·181))  (at level 60, right associativity). 
 Notation "·183":= (Next (·182))  (at level 60, right associativity). 
 Notation "·184":= (Next (·183))  (at level 60, right associativity). 
 Notation "·185":= (Next (·184))  (at level 60, right associativity). 
 Notation "·186":= (Next (·185))  (at level 60, right associativity). 
 Notation "·187":= (Next (·186))  (at level 60, right associativity). 
 Notation "·188":= (Next (·187))  (at level 60, right associativity). 
 Notation "·189":= (Next (·188))  (at level 60, right associativity). 
 Notation "·190":= (Next (·189))  (at level 60, right associativity). 
 Notation "·191":= (Next (·190))  (at level 60, right associativity). 
 Notation "·192":= (Next (·191))  (at level 60, right associativity). 
 Notation "·193":= (Next (·192))  (at level 60, right associativity). 
 Notation "·194":= (Next (·193))  (at level 60, right associativity). 
 Notation "·195":= (Next (·194))  (at level 60, right associativity). 
 Notation "·196":= (Next (·195))  (at level 60, right associativity). 
 Notation "·197":= (Next (·196))  (at level 60, right associativity). 
 Notation "·198":= (Next (·197))  (at level 60, right associativity). 
 Notation "·199":= (Next (·198))  (at level 60, right associativity). 
 Notation "·200":= (Next (·199))  (at level 60, right associativity). 
 Notation "·201":= (Next (·200))  (at level 60, right associativity). 
 Notation "·202":= (Next (·201))  (at level 60, right associativity). 
 Notation "·203":= (Next (·202))  (at level 60, right associativity). 
 Notation "·204":= (Next (·203))  (at level 60, right associativity). 
 Notation "·205":= (Next (·204))  (at level 60, right associativity). 
 Notation "·206":= (Next (·205))  (at level 60, right associativity). 
 Notation "·207":= (Next (·206))  (at level 60, right associativity). 
 Notation "·208":= (Next (·207))  (at level 60, right associativity). 
 Notation "·209":= (Next (·208))  (at level 60, right associativity). 
 Notation "·210":= (Next (·209))  (at level 60, right associativity). 
 Notation "·211":= (Next (·210))  (at level 60, right associativity). 
 Notation "·212":= (Next (·211))  (at level 60, right associativity). 
 Notation "·213":= (Next (·212))  (at level 60, right associativity). 
 Notation "·214":= (Next (·213))  (at level 60, right associativity). 
 Notation "·215":= (Next (·214))  (at level 60, right associativity). 
 Notation "·216":= (Next (·215))  (at level 60, right associativity). 
 Notation "·217":= (Next (·216))  (at level 60, right associativity). 
 Notation "·218":= (Next (·217))  (at level 60, right associativity). 
 Notation "·219":= (Next (·218))  (at level 60, right associativity). 
 Notation "·220":= (Next (·219))  (at level 60, right associativity). 
 Notation "·221":= (Next (·220))  (at level 60, right associativity). 
 Notation "·222":= (Next (·221))  (at level 60, right associativity). 
 Notation "·223":= (Next (·222))  (at level 60, right associativity). 
 Notation "·224":= (Next (·223))  (at level 60, right associativity). 
 Notation "·225":= (Next (·224))  (at level 60, right associativity). 
 Notation "·226":= (Next (·225))  (at level 60, right associativity). 
 Notation "·227":= (Next (·226))  (at level 60, right associativity). 
 Notation "·228":= (Next (·227))  (at level 60, right associativity). 
 Notation "·229":= (Next (·228))  (at level 60, right associativity). 
 Notation "·230":= (Next (·229))  (at level 60, right associativity). 
 Notation "·231":= (Next (·230))  (at level 60, right associativity). 
 Notation "·232":= (Next (·231))  (at level 60, right associativity). 
 Notation "·233":= (Next (·232))  (at level 60, right associativity). 
 Notation "·234":= (Next (·233))  (at level 60, right associativity). 
 Notation "·235":= (Next (·234))  (at level 60, right associativity). 
 Notation "·236":= (Next (·235))  (at level 60, right associativity). 
 Notation "·237":= (Next (·236))  (at level 60, right associativity). 
 Notation "·238":= (Next (·237))  (at level 60, right associativity). 
 Notation "·239":= (Next (·238))  (at level 60, right associativity). 
 Notation "·240":= (Next (·239))  (at level 60, right associativity). 
 Notation "·241":= (Next (·240))  (at level 60, right associativity). 
 Notation "·242":= (Next (·241))  (at level 60, right associativity). 
 Notation "·243":= (Next (·242))  (at level 60, right associativity). 
 Notation "·244":= (Next (·243))  (at level 60, right associativity). 
 Notation "·245":= (Next (·244))  (at level 60, right associativity). 
 Notation "·246":= (Next (·245))  (at level 60, right associativity). 
 Notation "·247":= (Next (·246))  (at level 60, right associativity). 
 Notation "·248":= (Next (·247))  (at level 60, right associativity). 
 Notation "·249":= (Next (·248))  (at level 60, right associativity). 
 Notation "·250":= (Next (·249))  (at level 60, right associativity). 
 

Section RecordsDefinitions.

Set Implicit Arguments.
Unset Strict Implicit.
Set Contextual Implicit.
Set Maximal Implicit Insertion.

Variables I I8 I16 I32 I64 I128 I256 : Type.
Variables A B C S: Type.
Variables L M: Type -> Type.
Variables HM P: Type -> Type -> Type.

Inductive ContractFunctionP  :=
| ContractFunctionDefault : ContractFunctionP
| DePoolContract_Ф_completeRoundF : I64 -> I32 -> ContractFunctionP
(* | DePoolContract_Ф_ticktockF : I64 -> I256 -> I32 -> I32 -> I256 -> I8 -> ContractFunctionP *)
| DePoolContract_Ф_completeRoundWithChunkF : I64 -> I8 -> ContractFunctionP
| DePoolContract_Ф_ticktockF : ContractFunctionP
| DePoolContract_Ф_onStakeAcceptF : I64 -> I32 -> A -> ContractFunctionP
| DePoolContract_Ф_onStakeRejectF : I64 -> I32 -> A -> ContractFunctionP
| DePoolContract_Ф_onSuccessToRecoverStakeF : I64 -> A -> ContractFunctionP
| DePoolContract_Ф_onFailToRecoverStakeF : I64 -> A -> ContractFunctionP
| DePoolContract_Ф_sendErrorF : I64 -> I32 -> ContractFunctionP
| DePoolContract_Ф_acceptRecoveredStakeF : I64 -> ContractFunctionP
| DePoolContract_Ф_terminatorF : ContractFunctionP 
 
| DePoolProxyContract_Ф_recover_stakeF : I64 -> A -> ContractFunctionP
| DePoolProxyContract_Ф_process_new_stakeF : I64 -> I256 -> I32 -> I32 -> I32 -> L I8 -> A -> ContractFunctionP

| ProxyBase_Ф_getProxyF : I64 -> ContractFunctionP

| IParticipant_И_receiveAnswerF : I32 -> I64 -> ContractFunctionP
| IParticipant_И_onRoundCompleteF : I64 -> I64 -> I64 -> I64 -> I64 -> B -> I8 -> ContractFunctionP
| IParticipant_И_onTransferF : A -> I128 -> ContractFunctionP

| ITimer_И_setTimerF : I -> ContractFunctionP

| IElector_И_process_new_stakeF : I64 -> I256 -> I32 -> I32 -> I32 -> L I8 -> ContractFunctionP
| IElector_И_recover_stakeF : I64 -> ContractFunctionP.

Inductive ContractFunctionWithId  :=
     
    | IProxy_И_recover_stakeF : ContractFunctionWithId
    | IProxy_И_process_new_stakeF : ContractFunctionWithId.


(* 	Definition T1 := DebugDePool . 
	Definition T2 := ValidatorBase . 
	Definition T3 := ProxyBase . 
	Definition T4 := True . 
	Definition T5 := ParticipantBase . 
	Definition T6 := DePoolHelper . 
	Definition T7 := Errors . 
	Definition T8 := InternalErrors . 
	Definition T9 := DePoolLib . 
	Definition T10 := DePoolProxyContract .  
	Definition T11 := RoundsBase . 
	Definition T12 := DePoolContract . 
	Definition T13 := True . 
	Definition T14 := True . 
	Definition T15 := TestElector . 
	Definition T16 := VMState . 
	Definition T17 := LocalState .  *)

Inductive DeployableContract := NullContractD | DePoolProxyContractD | DePoolContractD .



Record MessageStructP := MessageStructC
	{
		messageFlag: I8;
		messageBounce: B;
		messageValue: I256
	}.

Record ContractsFunctionWithMessageP := ContractsFunctionWithMessageC
	{
		contractAddress : A;
		contractFunction: ContractFunctionP ;
		contractMessage : MessageStructP 
	}.

Record ConstructorMessageP := ConstructorMessageC 
	{
		cmessage_wid: I;
		cmessage_value: I64;
		cmessage_stateInit: C  
	}.	


Inductive RoundsBase_ι_RoundStepP := 
 | RoundsBase_ι_RoundStepP_ι_Pooling : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingValidationStart : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingReward : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_Completing : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_Completed : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_PrePooling : RoundsBase_ι_RoundStepP. 

 Definition RoundsBase_ι_RoundStep := RoundsBase_ι_RoundStepP.
 
 
 Inductive RoundsBase_ι_CompletionReasonP := 
 | RoundsBase_ι_CompletionReasonP_ι_Undefined : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_PoolClosed : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_FakeRound : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_StakeIsRejectedByElector : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_ElectionsAreLost : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_NoValidatorRequest : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_BadProxy : RoundsBase_ι_CompletionReasonP . 

Definition RoundsBase_ι_CompletionReason := RoundsBase_ι_CompletionReasonP.

Record DePool_ι_LastRoundInfoP := DePool_ι_LastRoundInfoC {
  DePool_ι_LastRoundInfo_ι_supposedElectedAt : I32 ;
  DePool_ι_LastRoundInfo_ι_participantRewardFraction : I8 ;
  DePool_ι_LastRoundInfo_ι_validatorRewardFraction : I8 ;
  DePool_ι_LastRoundInfo_ι_participantQty : I32 ;
  DePool_ι_LastRoundInfo_ι_roundStake : I64 ;
  DePool_ι_LastRoundInfo_ι_validatorWallet : A ;
  DePool_ι_LastRoundInfo_ι_validatorPubkey : I256 ;
  DePool_ι_LastRoundInfo_ι_validatorAssurance : I64 ;
  DePool_ι_LastRoundInfo_ι_reward : I64 ;
  DePool_ι_LastRoundInfo_ι_reason : RoundsBase_ι_CompletionReasonP ;
  DePool_ι_LastRoundInfo_ι_isDePoolClosed : B 
}.

Record DePoolLib_ι_ParticipantP := DePoolLib_ι_ParticipantC  { 
 	DePoolLib_ι_Participant_ι_roundQty : I8  ;  
 	DePoolLib_ι_Participant_ι_reward : I64  ;  
 	DePoolLib_ι_Participant_ι_haveVesting : B  ;  
 	DePoolLib_ι_Participant_ι_haveLock : B  ;  
 	DePoolLib_ι_Participant_ι_reinvest : B  ;  
 	DePoolLib_ι_Participant_ι_withdrawValue : I64   
  }  .  

(*  Arguments DePoolLib_ι_ParticipantC  [  I8 I64 B  ]   . *)

 Record ValidatorBaseP  := ValidatorBaseC  { 
 	ValidatorBase_ι_m_validatorWallet : A  
 } . 
 
(*  Arguments ValidatorBaseC  [  A  ]   .  *)

 Record ProxyBaseP := ProxyBaseC  { 
 	ProxyBase_ι_m_proxies : HM I A  
 }   . 
 
(* Arguments ProxyBaseC  [  I A  HM]   . *)

Record ParticipantBaseP  := ParticipantBaseC  { 
 	ParticipantBase_ι_m_participants : HM A DePoolLib_ι_ParticipantP   
 } . 
 
(*  Arguments ParticipantBaseC  [ HM A I8 I64 B ] .  *)

 Record DePoolLib_ι_RequestP   := DePoolLib_ι_RequestC  { 
 	DePoolLib_ι_Request_ι_queryId : I64  ;  
 	DePoolLib_ι_Request_ι_validatorKey : I256  ;  
 	DePoolLib_ι_Request_ι_stakeAt : I32  ;  
 	DePoolLib_ι_Request_ι_maxFactor : I32  ;  
 	DePoolLib_ι_Request_ι_adnlAddr : I256  ;  
 	DePoolLib_ι_Request_ι_signature :  L I8   
  }  .  
(*  Arguments DePoolLib_ι_RequestC  [  I64 I256 I32 I8  L ]   . *)

Record DePoolProxyContractP := DePoolProxyContractC  { 
 	(* DePoolProxyContract_ι_ERROR_IS_NOT_DEPOOL : I  ;  *)  (* constant := 102  ;  *) 
 	(* DePoolProxyContract_ι_ERROR_BAD_BALANCE : I  ;   (* constant := 103  ;  *)  *)
 	DePoolProxyContract_ι_m_dePool : A  
 }   . 
(*  Arguments DePoolProxyContractC  [  I64 I A  ]   .  *)

Record RoundsBase_ι_InvestParamsP  := RoundsBase_ι_InvestParamsC  { 
 	RoundsBase_ι_InvestParams_ι_remainingAmount : I64  ;  
 	RoundsBase_ι_InvestParams_ι_lastWithdrawalTime : I64  ;  
 	RoundsBase_ι_InvestParams_ι_withdrawalPeriod : I32  ;  
 	RoundsBase_ι_InvestParams_ι_withdrawalValue : I64  ;  
 	RoundsBase_ι_InvestParams_ι_owner : A   
  }  .  
 (*  Arguments RoundsBase_ι_InvestParamsC  [  B I64 I32 A  ]   . *) 
 
Record RoundsBase_ι_StakeValueP  := RoundsBase_ι_StakeValueC  { 
	 RoundsBase_ι_StakeValue_ι_ordinary : I64;
	 RoundsBase_ι_StakeValue_ι_vesting : M RoundsBase_ι_InvestParamsP ;
   RoundsBase_ι_StakeValue_ι_lock : M RoundsBase_ι_InvestParamsP 
    }  .  
(* Arguments RoundsBase_ι_StakeValueC  [ B I64 I32 A M  ]   . *)


 Record RoundsBase_ι_RoundP := RoundsBase_ι_RoundC  { 
 	RoundsBase_ι_Round_ι_id : I64  ;  
 	RoundsBase_ι_Round_ι_supposedElectedAt : I32  ;  
 	RoundsBase_ι_Round_ι_unfreeze : I32  ;  
	RoundsBase_ι_Round_ι_stakeHeldFor : I32  ;
 	RoundsBase_ι_Round_ι_vsetHashInElectionPhase : I256  ;  
 	RoundsBase_ι_Round_ι_step : RoundsBase_ι_RoundStepP  ;  
 	RoundsBase_ι_Round_ι_completionReason : RoundsBase_ι_CompletionReasonP  ;  
 	RoundsBase_ι_Round_ι_stake : I64  ;  
	RoundsBase_ι_Round_ι_recoveredStake : I64 ;
	RoundsBase_ι_Round_ι_unused : I64  ;
	RoundsBase_ι_Round_ι_isValidatorStakeCompleted : B ;
	RoundsBase_ι_Round_ι_grossReward : I64 ;
 	RoundsBase_ι_Round_ι_rewards : I64  ;  
 	RoundsBase_ι_Round_ι_participantQty : I32  ;  
	RoundsBase_ι_Round_ι_stakes : HM A RoundsBase_ι_StakeValueP ;  
	RoundsBase_ι_Round_ι_validatorStake : I64;
	RoundsBase_ι_Round_ι_validatorRemainingStake : I64 ;
	RoundsBase_ι_Round_ι_handledStakesAndRewards : I64 ;
	RoundsBase_ι_Round_ι_validatorRequest : DePoolLib_ι_RequestP ;
  RoundsBase_ι_Round_ι_elector : A  ;  
 	RoundsBase_ι_Round_ι_proxy : A ;

 	RoundsBase_ι_Round_ι_validatorsElectedFor : I32
 } . 
(*  Arguments RoundsBase_ι_RoundC  [ I8 I64 I32 HM M L A I256 B] .  *)
	
 Record RoundsBase_ι_TruncatedRoundP  := RoundsBase_ι_TruncatedRoundC  { 
 	RoundsBase_ι_TruncatedRound_ι_id : I64  ;  
 	RoundsBase_ι_TruncatedRound_ι_supposedElectedAt : I32  ;  
 	RoundsBase_ι_TruncatedRound_ι_unfreeze : I32  ;  
	RoundsBase_ι_TruncatedRound_ι_stakeHeldFor : I32 ;
	RoundsBase_ι_TruncatedRound_ι_vsetHashInElectionPhase : I256 ;
 	RoundsBase_ι_TruncatedRound_ι_step : RoundsBase_ι_RoundStepP  ;  
 	RoundsBase_ι_TruncatedRound_ι_completionReason : RoundsBase_ι_CompletionReasonP  ;  
 	RoundsBase_ι_TruncatedRound_ι_stake : I64  ;  
	RoundsBase_ι_TruncatedRound_ι_recoveredStake : I64 ;
 	RoundsBase_ι_TruncatedRound_ι_unused : I64  ;  
	RoundsBase_ι_TruncatedRound_ι_isValidatorStakeCompleted : B ;
	RoundsBase_ι_TruncatedRound_ι_rewards : I64  ;  
 	RoundsBase_ι_TruncatedRound_ι_participantQty : I32  ;  
	RoundsBase_ι_TruncatedRound_ι_validatorStake : I64;
	RoundsBase_ι_TruncatedRound_ι_validatorRemainingStake : I64;
	RoundsBase_ι_TruncatedRound_ι_handledStakesAndRewards : I64
  } .  
(*  Arguments RoundsBase_ι_TruncatedRoundC  [ I64 I32 I256 B ] .  *)

Inductive LedgerEventP  := 
| NoEvent : LedgerEventP
| DePoolClosed : LedgerEventP
| roundStakeIsAccepted: I64 -> I32 -> LedgerEventP
| roundStakeIsRejected: I64 -> I32 -> LedgerEventP
| ProxyHasRejectedTheStake: I64 -> LedgerEventP
| ProxyHasRejectedRecoverRequest: I64 -> LedgerEventP
| RoundCompleted: RoundsBase_ι_TruncatedRoundP -> LedgerEventP
| StakeSigningRequested: I32 -> A -> LedgerEventP
| BadProxy : A -> LedgerEventP
| TooLowDePoolBalance : I -> LedgerEventP 
| RewardFractionsChanged : I8 -> I8 -> LedgerEventP .

Record RoundsBaseP  := RoundsBaseC  { 
 	RoundsBase_ι_m_rounds : HM I64 RoundsBase_ι_RoundP  ; 
 	RoundsBase_ι_m_roundQty : I64  ;   (* := 0  ;  *) 
(* mapping(bool => LastRoundInfo) lastRoundInfo; *)
    RoundsBase_ι_lastRoundInfo : HM B DePool_ι_LastRoundInfoP 
 } . 
 
(*  Arguments RoundsBaseC  [ HM M L I8 I64 I32 A I256 B] . *)

 Record DePoolContractP   := DePoolContractC  { 
 	DePoolContract_ι_m_poolClosed : B  ; 
 	DePoolContract_ι_m_minStake : I64  ; 
	DePoolContract_ι_m_validatorAssurance : I64 ;
	DePoolContract_ι_m_participantRewardFraction : I8 ;
	DePoolContract_ι_m_validatorRewardFraction : I8 ;
	DePoolContract_ι_m_balanceThreshold : I64 ;
(* 	DePoolContract_ι_CRITICAL_THRESHOLD : I64 (* constant := 5 ton  ;  *) *)
 }   . 
(*  Arguments DePoolContractC  [  I8 I64 I16 I32 B  ]   .  *)

Record TestElector_ι_ValidatorP   := TestElector_ι_ValidatorC  { 
 	TestElector_ι_Validator_ι_stake : I64  ;  
 	TestElector_ι_Validator_ι_key : I256  ;  
 	TestElector_ι_Validator_ι_reward : I64  ;  
 	TestElector_ι_Validator_ι_qid : I64  ;  
 	TestElector_ι_Validator_ι_factor : I32  ;  
 	TestElector_ι_Validator_ι_adnl : I256  ;  
 	TestElector_ι_Validator_ι_signature : I8   
  }  .  
(*  Arguments TestElector_ι_ValidatorC  [  I64 I256 I32 I8  ]   .  *)

Record TransactionP  := TransactionC {
   txDest   : A ;
   txValue  : I256 ; 
   txBounce : B ;
   txFlags  : I8 ;
   txPayload: C 
}.  
 
Record VMCommittedP :=  VMCommittedC {
	VMCommitted_ι_ValidatorBase : ValidatorBaseP ; 
	VMCommitted_ι_ProxyBase : ProxyBaseP  ; 
	VMCommitted_ι_ParticipantBase : ParticipantBaseP   ; 
	VMCommitted_ι_DePoolProxyContract : DePoolProxyContractP  ; 
	VMCommitted_ι_RoundsBase : RoundsBaseP  ; 
	VMCommitted_ι_DePoolContract : DePoolContractP  ;
}.


Record VMStateP  := VMStateC  { 
	VMState_ι_pubkey : I256  ; 
	VMState_ι_msg_pubkey : I256  ; 
	VMState_ι_now : I64  ; 
	VMState_ι_logstr : S  ; 
	VMState_ι_balance : I128  ; 
	VMState_ι_address : A  ; 
	VMState_ι_ltime : I256  ; 
	VMState_ι_code : C  ; 
    VMState_ι_events : L  LedgerEventP ;   
	VMState_ι_savedDePoolContracts :  VMCommittedP  ;
    VMState_ι_msg_sender : A  ; 
 	VMState_ι_msg_value : I256 ; 
	VMState_ι_messages: L ContractsFunctionWithMessageP;
	VMState_ι_msg_data : C  ; 
	VMState_ι_transactions : L TransactionP ;

	VMState_ι_accepted : B;
	VMState_ι_reserved : I128;
	VMState_ι_currentCode : C ;

	(* VMState_ι_configParam15 : P (P (P (P I32 I32) I32) I32) B; *)
		VMState_ι_validatorsElectedFor : I32 ;
		VMState_ι_electionsStartBefore : I32 ;
		VMState_ι_electionsEndBefore : I32 ;
		VMState_ι_stakeHeldFor : I32 ;

	VMState_ι_curValidatorData : C ;
		VMState_ι_unknown34 : I8 ; 
		VMState_ι_utime_since : I32 ;
		VMState_ι_utime_until : I32 ;

	(* VMState_ι_rawConfigParam_32 : C ; *)
		VMState_ι_prevValidatorData : C ;

	VMState_ι_rawConfigParam_17 : C ;
		VMState_ι_unknown17_1 : I8 ; (*check the type*)
		VMState_ι_unknown17_2 : I8 ; 
		VMState_ι_unknown17_3 : I8 ; 
		VMState_ι_maxStakeFactor : I32;

	VMState_ι_rawConfigParam_1 : C ;
		VMState_ι_electorRawAddress: A ;
	
	VMState_ι_deployed : HM DeployableContract I	
} . 

(* Arguments VMStateC  [ A I256 I64 S I128 C L I I8 I16 I32 B] .   *)

Load "LocalStateDefinition.v".
 
 Record LedgerP := LedgerC  { 
 	Ledger_ι_ValidatorBase : ValidatorBaseP  ; 
 	Ledger_ι_ProxyBase : ProxyBaseP ; 
  	Ledger_ι_ParticipantBase : ParticipantBaseP  ; 
 	Ledger_ι_DePoolProxyContract : DePoolProxyContractP  ; 
 	Ledger_ι_RoundsBase : RoundsBaseP   ; 
 	Ledger_ι_DePoolContract : DePoolContractP  ; 
  	Ledger_ι_VMState : VMStateP  ; 
 	Ledger_ι_LocalState : LocalStateP   
 }   . 
 
(* Arguments LedgerC [ I32 A HM P I8 I64 B I I256 I16 S I128 C L M ] . *)  
End RecordsDefinitions. 

Module LedgerClass (xt: XTypesSig) (sm: StateMonadSig) .
Module SolidityNotations := SolidityNotations.SolidityNotations xt sm.
Import SolidityNotations.
Existing Instance monadStateT. 
Existing Instance monadStateStateT.

(* Print DePool_ι_LastRoundInfoP. *)
Definition DePool_ι_LastRoundInfo := DePool_ι_LastRoundInfoP XInteger8 XInteger32 XInteger64 XInteger256 XAddress XBool .
(* Print ContractsFunctionWithMessageP. *)
Definition ContractsFunctionWithMessage := ContractsFunctionWithMessageP XInteger XInteger8 XInteger32 XInteger64 XInteger128 XInteger256 XAddress XBool XList.
(* Print ConstructorMessageP. *)
Definition ConstructorMessage := ConstructorMessageP XInteger XInteger64 TvmCell.
(* Print MessageStructP. *)
Definition MessageStruct := MessageStructP XInteger8 XInteger256 XBool.
(* Print ContractFunctionP.  *)
Definition ContractFunction := ContractFunctionP XInteger XInteger8 XInteger32 XInteger64 XInteger128 XInteger256 XAddress XBool XList .
(* Print LedgerEventP. *)
Definition LedgerEvent := LedgerEventP XInteger XInteger8 XInteger32 XInteger64 XInteger256 XAddress XBool.

Instance RoundsBase_ι_RoundStep_default : XDefault RoundsBase_ι_RoundStep := { 
	default := RoundsBase_ι_RoundStepP_ι_Pooling } . 
	
Instance RoundsBase_ι_CompletionReason_default : XDefault RoundsBase_ι_CompletionReason := { 
	default := RoundsBase_ι_CompletionReasonP_ι_Undefined } . 
 
Instance event_default : XDefault LedgerEvent :=  { 
	default:= NoEvent }.

Instance MessageStruct_default : XDefault MessageStruct := {
	default := MessageStructC default default default }.

Instance ContractFunction_default : XDefault ContractFunction := {
	default := ContractFunctionDefault}.

Instance ContractsFunctionWithMessage_default : XDefault ContractsFunctionWithMessage := {
	default := ContractsFunctionWithMessageC default default default}.

Instance ConstructorMessage_default : XDefault 	ConstructorMessage := {
	default := ConstructorMessageC default default default
}.

Global Instance Struct_ConstructorMessage : Struct ConstructorMessage :=  { 
 	fields :=  [ 
 		@existT _ _ _ cmessage_wid , 
 		@existT _ _ _ cmessage_value , 
 		@existT _ _ _ cmessage_stateInit
 	 ]   ;  
 	 ctor := ConstructorMessageC 
 }   . 
Global Instance Acc_MessageStruct_ι_cmessage_wid : Accessor cmessage_wid :=  {  acc := ·0  }   . 
Global Instance Acc_MessageStruct_ι_cmessage_value : Accessor cmessage_value :=  {  acc := ·1  }   . 
Global Instance Acc_MessageStruct_ι_cmessage_stateInit : Accessor cmessage_stateInit :=  {  acc := ·2  }   . 


Global Instance Struct_MessageStruct : Struct MessageStruct :=  { 
 	fields :=  [ 
 		@existT _ _ _ messageFlag , 
 		@existT _ _ _ messageBounce , 
 		@existT _ _ _ messageValue 
 	 ]   ;  
 	 ctor := MessageStructC 
 }   . 
Global Instance Acc_MessageStruct_ι_messageFlag : Accessor messageFlag :=  {  acc := ·0  }   . 
Global Instance Acc_MessageStruct_ι_messageBounce : Accessor messageBounce :=  {  acc := ·1  }   . 
Global Instance Acc_MessageStruct_ι_messageValue : Accessor messageValue :=  {  acc := ·2  }   . 

Global Instance Struct_ContractsFunctionWithMessage : Struct ContractsFunctionWithMessage :=  { 
 	fields :=  [ 
 		@existT _ _ _ contractAddress , 
 		@existT _ _ _ contractFunction, 
 		@existT _ _ _ contractMessage 
 	 ]   ;  
 	 ctor := ContractsFunctionWithMessageC 
 }   . 
Global Instance Acc_ContractsFunctionWithMessage_ι_contractAddress : Accessor contractAddress :=  {  acc := ·0  }   . 
Global Instance Acc_ContractsFunctionWithMessage_ι_contractFunction : Accessor contractFunction :=  {  acc := ·1  }   . 
Global Instance Acc_ContractsFunctionWithMessage_ι_contractMessage : Accessor contractMessage :=  {  acc := ·2  }   . 


Global Instance Struct_DePool_ι_LastRoundInfo : Struct DePool_ι_LastRoundInfo := {
 	fields :=  [ 
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_supposedElectedAt ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_participantRewardFraction ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_validatorRewardFraction ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_participantQty  ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_roundStake ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_validatorWallet ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_validatorPubkey ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_validatorAssurance ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_reward ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_reason ,
 		@existT _ _ _ DePool_ι_LastRoundInfo_ι_isDePoolClosed  
 	 ]   ;  
 	 ctor := DePool_ι_LastRoundInfoC 
} .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_supposedElectedAt  : Accessor DePool_ι_LastRoundInfo_ι_supposedElectedAt :=  {  acc := ·0  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_participantRewardFraction  : Accessor DePool_ι_LastRoundInfo_ι_participantRewardFraction :=  {  acc := ·1  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_validatorRewardFraction  : Accessor DePool_ι_LastRoundInfo_ι_validatorRewardFraction :=  {  acc := ·2  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_participantQty  : Accessor DePool_ι_LastRoundInfo_ι_participantQty :=  {  acc := ·3  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_roundStake  : Accessor DePool_ι_LastRoundInfo_ι_roundStake :=  {  acc := ·4  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_validatorWallet  : Accessor DePool_ι_LastRoundInfo_ι_validatorWallet :=  {  acc := ·5  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_validatorPubkey  : Accessor DePool_ι_LastRoundInfo_ι_validatorPubkey :=  {  acc := ·6  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_validatorAssurance  : Accessor DePool_ι_LastRoundInfo_ι_validatorAssurance :=  {  acc := ·7  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_reward  : Accessor DePool_ι_LastRoundInfo_ι_reward :=  {  acc := ·8  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_reason  : Accessor DePool_ι_LastRoundInfo_ι_reason  :=  {  acc := ·9  }   .
Global Instance Acc_DePool_ι_LastRoundInfo_ι_isDePoolClosed  : Accessor DePool_ι_LastRoundInfo_ι_isDePoolClosed  :=  {  acc := ·10  }   .

Instance DePool_ι_LastRoundInfo_default : XDefault DePool_ι_LastRoundInfo :=  {  
 	 default := DePool_ι_LastRoundInfoC default default default default default 
                                      default default default default default
                                      default
  }   . 

Definition ValidatorBase := @ValidatorBaseP XAddress . 
Global Instance Struct_ValidatorBase : Struct ValidatorBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ ValidatorBase_ι_m_validatorWallet 
 
 	 ]   ;  
 	 ctor := ValidatorBaseC 
 }   . 
Global Instance Acc_ValidatorBase_ι_m_validatorWallet : Accessor ValidatorBase_ι_m_validatorWallet :=  {  acc := ·0  }   . 
Instance ValidatorBase_default : XDefault ValidatorBase :=  {  
 	 default := ValidatorBaseC default  
  }   . 
(* Definition ValidatorBaseT := StateT ValidatorBase . *) 
 
(* Print ProxyBaseP.  *) 
Definition ProxyBase := @ProxyBaseP XInteger XAddress XHMap. 
Global Instance Struct_ProxyBase : Struct ProxyBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ ProxyBase_ι_m_proxies 
 
 	 ]   ;  
 	 ctor := ProxyBaseC 
 }   . 
Global Instance Acc_ProxyBase_ι_m_proxy0 : Accessor ProxyBase_ι_m_proxies :=  {  acc := ·0  }   . 
 
Instance ProxyBase_default : XDefault ProxyBase :=  {  
 	 default := ProxyBaseC default   
  }   . 
(* Definition ProxyBaseT := StateT ProxyBase . *) 
  
(* Print   ParticipantBaseP. *)
Definition ParticipantBase := @ParticipantBaseP XInteger8 XInteger64 XAddress XBool XHMap. 
Global Instance Struct_ParticipantBase : Struct ParticipantBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ ParticipantBase_ι_m_participants 
 	 ]   ;  
 	 ctor := ParticipantBaseC 
 }   . 
Global Instance Acc_ParticipantBase_ι_m_participants : Accessor ParticipantBase_ι_m_participants :=  {  acc := ·0  }   . 
Instance ParticipantBase_default : XDefault ParticipantBase :=  {  
 	 default := ParticipantBaseC default  
  }   . 
(* Definition ParticipantBaseT := StateT ParticipantBase . *) 
 
  
 
(* Print   DePoolLib_ι_ParticipantP. *)
Definition DePoolLib_ι_Participant := @DePoolLib_ι_ParticipantP XInteger8 XInteger64 XBool . 
Definition DePoolLib_ι_Request := @DePoolLib_ι_RequestP XInteger8 XInteger32 XInteger64 XInteger256 XList. 

Bind Scope struct_scope with DePoolLib_ι_Participant  . 
Bind Scope struct_scope with DePoolLib_ι_Request  . 
Global Instance Struct_DePoolLib_ι_Participant : Struct DePoolLib_ι_Participant :=  {  
 	 fields :=  [  
 		@existT _ _ _ DePoolLib_ι_Participant_ι_roundQty , 
 		@existT _ _ _ DePoolLib_ι_Participant_ι_reward , 
 		@existT _ _ _ DePoolLib_ι_Participant_ι_haveVesting , 
 		@existT _ _ _ DePoolLib_ι_Participant_ι_haveLock , 
 		@existT _ _ _ DePoolLib_ι_Participant_ι_reinvest , 
 		@existT _ _ _ DePoolLib_ι_Participant_ι_withdrawValue 
 	  ]   ;  
 	 ctor := DePoolLib_ι_ParticipantC 
 }   . 
Global Instance Acc_DePoolLib_ι_Participant_ι_roundQty : Accessor DePoolLib_ι_Participant_ι_roundQty :=  {  acc := ·0  }   . 
Global Instance Acc_DePoolLib_ι_Participant_ι_reward : Accessor DePoolLib_ι_Participant_ι_reward :=  {  acc := ·1  }   . 
Global Instance Acc_DePoolLib_ι_Participant_ι_haveVesting : Accessor DePoolLib_ι_Participant_ι_haveVesting :=  {  acc := ·2  }   . 
Global Instance Acc_DePoolLib_ι_Participant_ι_haveLock : Accessor DePoolLib_ι_Participant_ι_haveLock :=  {  acc := ·3  }   . 
Global Instance Acc_DePoolLib_ι_Participant_ι_reinvest : Accessor DePoolLib_ι_Participant_ι_reinvest :=  {  acc := ·4  }   . 
Global Instance Acc_DePoolLib_ι_Participant_ι_withdrawValue : Accessor DePoolLib_ι_Participant_ι_withdrawValue :=  {  acc := ·5  }   . 
Global Instance Struct_DePoolLib_ι_Request : Struct DePoolLib_ι_Request :=  {  
 	 fields :=  [  
 		@existT _ _ _ DePoolLib_ι_Request_ι_queryId , 
 		@existT _ _ _ DePoolLib_ι_Request_ι_validatorKey , 
 		@existT _ _ _ DePoolLib_ι_Request_ι_stakeAt , 
 		@existT _ _ _ DePoolLib_ι_Request_ι_maxFactor , 
 		@existT _ _ _ DePoolLib_ι_Request_ι_adnlAddr , 
 		@existT _ _ _ DePoolLib_ι_Request_ι_signature 
 	  ]   ;  
 	 ctor := DePoolLib_ι_RequestC 
 }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_queryId : Accessor DePoolLib_ι_Request_ι_queryId :=  {  acc := ·0  }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_validatorKey : Accessor DePoolLib_ι_Request_ι_validatorKey :=  {  acc := ·1  }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_stakeAt : Accessor DePoolLib_ι_Request_ι_stakeAt :=  {  acc := ·2  }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_maxFactor : Accessor DePoolLib_ι_Request_ι_maxFactor :=  {  acc := ·3  }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_adnlAddr : Accessor DePoolLib_ι_Request_ι_adnlAddr :=  {  acc := ·4  }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_signature : Accessor DePoolLib_ι_Request_ι_signature :=  {  acc := ·5  }   . 

Instance DePoolLib_ι_Participant_default : XDefault DePoolLib_ι_Participant :=  {  
 	 default := DePoolLib_ι_ParticipantC default default default default default default 
  }   . 
Instance DePoolLib_ι_Request_default : XDefault DePoolLib_ι_Request :=  {  
 	 default := DePoolLib_ι_RequestC default default default default default default  
  }   . 

Definition DePoolProxyContract := @DePoolProxyContractP XAddress . 


Global Instance Struct_DePoolProxyContract : Struct DePoolProxyContract :=  { 
 	fields :=  [ 
 		@existT _ _ _ DePoolProxyContract_ι_m_dePool 
 	 ]   ;  
 	 ctor := DePoolProxyContractC 
 }   . 
Global Instance Acc_DePoolProxyContract_ι_m_dePool : Accessor DePoolProxyContract_ι_m_dePool :=  {  acc := ·0  }   . 
Instance DePoolProxyContract_default : XDefault DePoolProxyContract :=  {  
 	 default := DePoolProxyContractC default   
  }   . 
(* Definition DePoolProxyContractT := StateT DePoolProxyContract . *) 
 
  
 Definition RoundsBase_ι_InvestParams := @RoundsBase_ι_InvestParamsP XInteger32 XInteger64 XAddress . 
 Definition RoundsBase_ι_StakeValue := @RoundsBase_ι_StakeValueP  XInteger32 XInteger64  XAddress (* XBool *) XMaybe . 
 Definition RoundsBase_ι_Round := @RoundsBase_ι_RoundP XInteger8 XInteger32 XInteger64 XInteger256 XAddress XBool  XList XMaybe  XHMap . 
 Definition RoundsBase_ι_TruncatedRound := @RoundsBase_ι_TruncatedRoundP XInteger32 XInteger64 XInteger256 XBool. 
 Definition RoundsBase := @RoundsBaseP XInteger8 XInteger32 XInteger64 XInteger256 XAddress XBool   XList  XMaybe XHMap . 

 Bind Scope struct_scope with RoundsBase_ι_InvestParams  . 
 Bind Scope struct_scope with RoundsBase_ι_StakeValue  . 
 Bind Scope struct_scope with RoundsBase_ι_Round  . 
 Bind Scope struct_scope with RoundsBase_ι_TruncatedRound  . 
Global Instance Struct_RoundsBase_ι_InvestParams : Struct RoundsBase_ι_InvestParams :=  {  
 	 fields :=  [  
 	(* 	@existT _ _ _ RoundsBase_ι_InvestParams_ι_isActive ,  *)
 		@existT _ _ _ RoundsBase_ι_InvestParams_ι_remainingAmount , 
 		@existT _ _ _ RoundsBase_ι_InvestParams_ι_lastWithdrawalTime , 
 		@existT _ _ _ RoundsBase_ι_InvestParams_ι_withdrawalPeriod , 
 		@existT _ _ _ RoundsBase_ι_InvestParams_ι_withdrawalValue , 
 		@existT _ _ _ RoundsBase_ι_InvestParams_ι_owner 
 	  ]   ;  
 	 ctor := RoundsBase_ι_InvestParamsC 
 }   . 
(* Global Instance Acc_RoundsBase_ι_InvestParams_ι_isActive : Accessor RoundsBase_ι_InvestParams_ι_isActive :=  {  acc := ·0  }   . 
 *)Global Instance Acc_RoundsBase_ι_InvestParams_ι_remainingAmount : Accessor RoundsBase_ι_InvestParams_ι_remainingAmount :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase_ι_InvestParams_ι_lastWithdrawalTime : Accessor RoundsBase_ι_InvestParams_ι_lastWithdrawalTime :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase_ι_InvestParams_ι_withdrawalPeriod : Accessor RoundsBase_ι_InvestParams_ι_withdrawalPeriod :=  {  acc := ·2  }   . 
Global Instance Acc_RoundsBase_ι_InvestParams_ι_withdrawalValue : Accessor RoundsBase_ι_InvestParams_ι_withdrawalValue :=  {  acc := ·3  }   . 
Global Instance Acc_RoundsBase_ι_InvestParams_ι_owner : Accessor RoundsBase_ι_InvestParams_ι_owner :=  {  acc := ·4  }   . 
Global Instance Struct_RoundsBase_ι_StakeValue : Struct RoundsBase_ι_StakeValue :=  {  
 	 fields :=  [  
		 @existT _ _ _ RoundsBase_ι_StakeValue_ι_ordinary ,
		 @existT _ _ _ RoundsBase_ι_StakeValue_ι_vesting ,
		 @existT _ _ _ RoundsBase_ι_StakeValue_ι_lock
 	  ]   ;  
 	 ctor := RoundsBase_ι_StakeValueC 
 }   . 
Global Instance Acc_RoundsBase_ι_StakeValue_ι_ordinary : Accessor RoundsBase_ι_StakeValue_ι_ordinary :=  {  acc := ·0  }   .
Global Instance Acc_RoundsBase_ι_StakeValue_ι_vesting : Accessor RoundsBase_ι_StakeValue_ι_vesting :=  {  acc := ·1  }   .
Global Instance Acc_RoundsBase_ι_StakeValue_ι_lock : Accessor RoundsBase_ι_StakeValue_ι_lock :=  {  acc := ·2  }   . 

Global Instance Struct_RoundsBase_ι_Round : Struct RoundsBase_ι_Round :=  {  
 	 fields :=  [  
 		@existT _ _ _ RoundsBase_ι_Round_ι_id , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_supposedElectedAt , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_unfreeze , 
		@existT _ _ _ RoundsBase_ι_Round_ι_stakeHeldFor ,
 		@existT _ _ _ RoundsBase_ι_Round_ι_vsetHashInElectionPhase , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_step , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_completionReason , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_stake , 
		@existT _ _ _ RoundsBase_ι_Round_ι_recoveredStake ,
		@existT _ _ _ RoundsBase_ι_Round_ι_unused ,
		@existT _ _ _ RoundsBase_ι_Round_ι_isValidatorStakeCompleted ,
		@existT _ _ _ RoundsBase_ι_Round_ι_grossReward ,
		@existT _ _ _ RoundsBase_ι_Round_ι_rewards , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_participantQty , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_stakes , 
		@existT _ _ _ RoundsBase_ι_Round_ι_validatorStake ,
		@existT _ _ _ RoundsBase_ι_Round_ι_validatorRemainingStake ,
		@existT _ _ _ RoundsBase_ι_Round_ι_handledStakesAndRewards ,
		@existT _ _ _ RoundsBase_ι_Round_ι_validatorRequest ,
 
 		@existT _ _ _ RoundsBase_ι_Round_ι_elector , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_proxy ,
 		@existT _ _ _ RoundsBase_ι_Round_ι_validatorsElectedFor
	  ]   ;  
 	 ctor := RoundsBase_ι_RoundC 
 }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_id : Accessor RoundsBase_ι_Round_ι_id :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_supposedElectedAt : Accessor RoundsBase_ι_Round_ι_supposedElectedAt :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_unfreeze : Accessor RoundsBase_ι_Round_ι_unfreeze :=  {  acc := ·2  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_stakeHeldFor : Accessor RoundsBase_ι_Round_ι_stakeHeldFor :=  {  acc := ·3  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_vsetHashInElectionPhase : Accessor RoundsBase_ι_Round_ι_vsetHashInElectionPhase :=  {  acc := ·4  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_step : Accessor RoundsBase_ι_Round_ι_step :=  {  acc := ·5  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_completionReason : Accessor RoundsBase_ι_Round_ι_completionReason :=  {  acc := ·6  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_stake : Accessor RoundsBase_ι_Round_ι_stake :=  {  acc := ·7  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_recoveredStake : Accessor RoundsBase_ι_Round_ι_recoveredStake :=  {  acc := ·8  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_unused : Accessor RoundsBase_ι_Round_ι_unused :=  {  acc := ·9  }   .
Global Instance Acc_RoundsBase_ι_Round_ι_isValidatorStakeCompleted : Accessor RoundsBase_ι_Round_ι_isValidatorStakeCompleted :=  {  acc := ·10  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_grossReward :  Accessor RoundsBase_ι_Round_ι_grossReward :=  {  acc := ·11  }   .
Global Instance Acc_RoundsBase_ι_Round_ι_rewards : Accessor RoundsBase_ι_Round_ι_rewards :=  {  acc := ·12  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_participantQty : Accessor RoundsBase_ι_Round_ι_participantQty :=  {  acc := ·13  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_stakes : Accessor RoundsBase_ι_Round_ι_stakes :=  {  acc := ·14  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_validatorStake : Accessor RoundsBase_ι_Round_ι_validatorStake :=  {  acc := ·15  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_validatorRemainingStake : Accessor RoundsBase_ι_Round_ι_validatorRemainingStake :=  {  acc := ·16  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_handledStakesAndRewards : Accessor RoundsBase_ι_Round_ι_handledStakesAndRewards :=  {  acc := ·17  }   .
Global Instance Acc_RoundsBase_ι_Round_ι_validatorRequest : Accessor RoundsBase_ι_Round_ι_validatorRequest :=  {  acc := ·18  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_elector : Accessor RoundsBase_ι_Round_ι_elector :=  {  acc := ·19  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_proxy : Accessor RoundsBase_ι_Round_ι_proxy :=  {  acc := ·20  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_validatorsElectedFor : Accessor RoundsBase_ι_Round_ι_validatorsElectedFor :=  {  acc := ·21  }   . 
 
Global Instance Struct_RoundsBase_ι_TruncatedRound : Struct RoundsBase_ι_TruncatedRound :=  {  
 	 fields :=  [  
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_id , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_supposedElectedAt , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_unfreeze , 
		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_stakeHeldFor ,
		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_vsetHashInElectionPhase ,
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_step , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_completionReason , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_stake , 
		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_recoveredStake ,
		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_unused , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_isValidatorStakeCompleted ,
		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_rewards , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_participantQty , 
		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_validatorStake ,
		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_validatorRemainingStake ,
		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_handledStakesAndRewards 
 	  ]   ;  
 	 ctor := RoundsBase_ι_TruncatedRoundC 
 }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_id : Accessor RoundsBase_ι_TruncatedRound_ι_id :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_supposedElectedAt : Accessor RoundsBase_ι_TruncatedRound_ι_supposedElectedAt :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_unfreeze : Accessor RoundsBase_ι_TruncatedRound_ι_unfreeze :=  {  acc := ·2  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_stakeHeldFor : Accessor RoundsBase_ι_TruncatedRound_ι_stakeHeldFor :=  {  acc := ·3  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_vsetHashInElectionPhase : Accessor RoundsBase_ι_TruncatedRound_ι_vsetHashInElectionPhase :=  {  acc := ·4  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_step : Accessor RoundsBase_ι_TruncatedRound_ι_step :=  {  acc := ·5  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_completionReason : Accessor RoundsBase_ι_TruncatedRound_ι_completionReason :=  {  acc := ·6  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_stake : Accessor RoundsBase_ι_TruncatedRound_ι_stake :=  {  acc := ·7  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_recoveredStake : Accessor RoundsBase_ι_TruncatedRound_ι_recoveredStake :=  {  acc := ·8  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_unused : Accessor RoundsBase_ι_TruncatedRound_ι_unused :=  {  acc := ·9  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_isValidatorStakeCompleted : Accessor RoundsBase_ι_TruncatedRound_ι_isValidatorStakeCompleted :=  {  acc := ·10  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_rewards : Accessor RoundsBase_ι_TruncatedRound_ι_rewards :=  {  acc := ·11  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_participantQty : Accessor RoundsBase_ι_TruncatedRound_ι_participantQty :=  {  acc := ·12  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_validatorStake : Accessor RoundsBase_ι_TruncatedRound_ι_validatorStake :=  {  acc := ·13  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_validatorRemainingStake : Accessor RoundsBase_ι_TruncatedRound_ι_validatorRemainingStake :=  {  acc := ·14  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_handledStakesAndRewards : Accessor RoundsBase_ι_TruncatedRound_ι_handledStakesAndRewards :=  {  acc := ·15  }   . 


Global Instance Struct_RoundsBase : Struct RoundsBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ RoundsBase_ι_m_rounds , 
 		@existT _ _ _ RoundsBase_ι_m_roundQty ,
 		@existT _ _ _ RoundsBase_ι_lastRoundInfo
 	 ]   ;  
 	 ctor := RoundsBaseC 
 }   . 
Global Instance Acc_RoundsBase_ι_m_rounds : Accessor RoundsBase_ι_m_rounds :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase_ι_m_roundQty : Accessor RoundsBase_ι_m_roundQty :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase_ι_lastRoundInfo : Accessor RoundsBase_ι_lastRoundInfo := {  acc := ·2  }   . 

Instance RoundsBase_ι_InvestParams_default : XDefault RoundsBase_ι_InvestParams :=  {  
 	 default := RoundsBase_ι_InvestParamsC default default default default default (* default *)  
  }   . 
Instance RoundsBase_ι_StakeValue_default : XDefault RoundsBase_ι_StakeValue :=  {  
 	 default := RoundsBase_ι_StakeValueC default default default 
  }   . 

Instance RoundsBase_ι_Round_default : XDefault RoundsBase_ι_Round :=
 {
	  default := RoundsBase_ι_RoundC default default default default 
									 default default default default 
									 default default default default 
									 default default default default  
									 default default default default
                   default default
  }.

Instance RoundsBase_ι_TruncatedRound_default : XDefault RoundsBase_ι_TruncatedRound :=  {  
	  default := RoundsBase_ι_TruncatedRoundC default default default default 
												default default default default 
												default default default default  
												default default default default 
  }   . 
Instance RoundsBase_default : XDefault RoundsBase :=  {  
 	 default := RoundsBaseC default default default
  }   . 

(* Definition RoundsBaseT := StateT RoundsBase . *) 

Definition DePoolContract := @DePoolContractP  XInteger8 XInteger64 XBool .

Global Instance Struct_DePoolContract : Struct DePoolContract :=  { 
 	fields :=  [ 
 		@existT _ _ _ DePoolContract_ι_m_poolClosed , 
 		@existT _ _ _ DePoolContract_ι_m_minStake , 
		@existT _ _ _ DePoolContract_ι_m_validatorAssurance ,
		@existT _ _ _ DePoolContract_ι_m_participantRewardFraction ,
		@existT _ _ _ DePoolContract_ι_m_validatorRewardFraction ,
		@existT _ _ _ DePoolContract_ι_m_balanceThreshold 
 	 ]   ;  
 	 ctor := DePoolContractC 
 }   . 

Global Instance Acc_DePoolContract_ι_m_poolClosed : Accessor DePoolContract_ι_m_poolClosed :=  {  acc := ·0  }   . 
Global Instance Acc_DePoolContract_ι_m_minStake : Accessor DePoolContract_ι_m_minStake :=  {  acc := ·1  }   . 
Global Instance Acc_DePoolContract_ι_m_validatorAssurance : Accessor DePoolContract_ι_m_validatorAssurance := {  acc := ·2  }   .
Global Instance Acc_DePoolContract_ι_m_participantRewardFraction : Accessor DePoolContract_ι_m_participantRewardFraction := {  acc := ·3  }   .
Global Instance Acc_DePoolContract_ι_m_validatorRewardFraction : Accessor DePoolContract_ι_m_validatorRewardFraction := {  acc := ·4  }   .
Global Instance Acc_DePoolContract_ι_m_balanceThreshold : Accessor DePoolContract_ι_m_balanceThreshold := {  acc := ·5  }   .

Instance DePoolContract_default : XDefault DePoolContract :=  {  
	  default := DePoolContractC default default default default 
								               default default  
  }   . 
(* Definition DePoolContractT := StateT DePoolContract . *) 
    
  
Definition TestElector_ι_Validator := @TestElector_ι_ValidatorP XInteger8 XInteger32 XInteger64 XInteger256. 
Bind Scope struct_scope with TestElector_ι_Validator  . 
Global Instance Struct_TestElector_ι_Validator : Struct TestElector_ι_Validator :=  {  
 	 fields :=  [  
 		@existT _ _ _ TestElector_ι_Validator_ι_stake , 
 		@existT _ _ _ TestElector_ι_Validator_ι_key , 
 		@existT _ _ _ TestElector_ι_Validator_ι_reward , 
 		@existT _ _ _ TestElector_ι_Validator_ι_qid , 
 		@existT _ _ _ TestElector_ι_Validator_ι_factor , 
 		@existT _ _ _ TestElector_ι_Validator_ι_adnl , 
 		@existT _ _ _ TestElector_ι_Validator_ι_signature 
 	  ]   ;  
 	 ctor := TestElector_ι_ValidatorC 
 }   . 
Global Instance Acc_TestElector_ι_Validator_ι_stake : Accessor TestElector_ι_Validator_ι_stake :=  {  acc := ·0  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_key : Accessor TestElector_ι_Validator_ι_key :=  {  acc := ·1  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_reward : Accessor TestElector_ι_Validator_ι_reward :=  {  acc := ·2  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_qid : Accessor TestElector_ι_Validator_ι_qid :=  {  acc := ·3  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_factor : Accessor TestElector_ι_Validator_ι_factor :=  {  acc := ·4  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_adnl : Accessor TestElector_ι_Validator_ι_adnl :=  {  acc := ·5  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_signature : Accessor TestElector_ι_Validator_ι_signature :=  {  acc := ·6  }   . 

Definition  VMCommitted := @VMCommittedP XInteger XInteger8 XInteger32 XInteger64 XInteger256 XAddress XBool XList XMaybe XHMap .
Global Instance Struct_VMCommitted : Struct VMCommitted :=  { 
 	fields :=  [ 
		@existT _ _ _ VMCommitted_ι_ValidatorBase ,
		@existT _ _ _ VMCommitted_ι_ProxyBase ,
		@existT _ _ _ VMCommitted_ι_ParticipantBase ,
		@existT _ _ _ VMCommitted_ι_DePoolProxyContract ,
		@existT _ _ _ VMCommitted_ι_RoundsBase ,
		@existT _ _ _ VMCommitted_ι_DePoolContract 
	 ]   ;  
 	 ctor := VMCommittedC 
 }   . 


Global Instance Acc_VMCommitted_ι_ValidatorBase : Accessor VMCommitted_ι_ValidatorBase := {  acc := ·0  }   . 
Global Instance Acc_VMCommitted_ι_ProxyBase : Accessor VMCommitted_ι_ProxyBase := {  acc := ·1  }   . 
Global Instance Acc_VMCommitted_ι_ParticipantBase : Accessor VMCommitted_ι_ParticipantBase := {  acc := ·2  }   . 
Global Instance Acc_VMCommitted_ι_DePoolProxyContract : Accessor VMCommitted_ι_DePoolProxyContract := {  acc := ·3  }   . 
Global Instance Acc_VMCommitted_ι_RoundsBase : Accessor VMCommitted_ι_RoundsBase := {  acc := ·4  }   . 
Global Instance Acc_VMCommitted_ι_DePoolContract : Accessor VMCommitted_ι_DePoolContract := {  acc := ·5  }   . 
 


Instance VMCommitted_default : XDefault VMCommitted :=  {  
 default := VMCommittedC  default default default default  
                          default default  
  }   . 
 
Definition VMState := @VMStateP XInteger XInteger8 XInteger32 XInteger64 
								XInteger128 XInteger256 XAddress XBool TvmCell XString 
								XList XMaybe XHMap. 
Global Instance Struct_VMState : Struct VMState :=  { 
 	fields :=  [ 
 		@existT _ _ _ VMState_ι_pubkey , 
 		@existT _ _ _ VMState_ι_msg_pubkey , 
 		@existT _ _ _ VMState_ι_now , 
 		@existT _ _ _ VMState_ι_logstr , 
 		@existT _ _ _ VMState_ι_balance , 
 		@existT _ _ _ VMState_ι_address , 
 		@existT _ _ _ VMState_ι_ltime , 
 		@existT _ _ _ VMState_ι_code , 
 		@existT _ _ _ VMState_ι_events , 
		@existT _ _ _ VMState_ι_savedDePoolContracts , 
 		@existT _ _ _ VMState_ι_msg_sender , 
		@existT _ _ _ VMState_ι_msg_value ,
		@existT _ _ _ VMState_ι_messages , 
		@existT _ _ _ VMState_ι_msg_data , 
		@existT _ _ _ VMState_ι_transactions ,

		@existT _ _ _ VMState_ι_accepted ,
		@existT _ _ _ VMState_ι_reserved ,
		@existT _ _ _ VMState_ι_currentCode ,


		@existT _ _ _ VMState_ι_validatorsElectedFor ,
		@existT _ _ _ VMState_ι_electionsStartBefore ,
		@existT _ _ _ VMState_ι_electionsEndBefore ,
		@existT _ _ _ VMState_ι_stakeHeldFor ,
	
		@existT _ _ _ VMState_ι_curValidatorData ,
		@existT _ _ _ VMState_ι_unknown34 ,
		@existT _ _ _ VMState_ι_utime_since ,
		@existT _ _ _ VMState_ι_utime_until ,
	
		@existT _ _ _ VMState_ι_prevValidatorData ,
	
		@existT _ _ _ VMState_ι_rawConfigParam_17 ,
		@existT _ _ _ VMState_ι_unknown17_1 ,
		@existT _ _ _ VMState_ι_unknown17_2 ,
		@existT _ _ _ VMState_ι_unknown17_3 ,
		@existT _ _ _ VMState_ι_maxStakeFactor ,
	
		@existT _ _ _ VMState_ι_rawConfigParam_1 ,
		@existT _ _ _ VMState_ι_electorRawAddress ,
		@existT _ _ _  VMState_ι_deployed

 	 ]   ;  
 	 ctor := VMStateC 
 }   . 


Global Instance Acc_VMState_ι_pubkey : Accessor VMState_ι_pubkey :=  {  acc := ·0  }   . 
Global Instance Acc_VMState_ι_msg_pubkey : Accessor VMState_ι_msg_pubkey :=  {  acc := ·1  }   . 
Global Instance Acc_VMState_ι_now : Accessor VMState_ι_now :=  {  acc := ·2  }   . 
Global Instance Acc_VMState_ι_logstr : Accessor VMState_ι_logstr :=  {  acc := ·3  }   . 
Global Instance Acc_VMState_ι_balance : Accessor VMState_ι_balance :=  {  acc := ·4  }   . 
Global Instance Acc_VMState_ι_address : Accessor VMState_ι_address :=  {  acc := ·5  }   . 
Global Instance Acc_VMState_ι_ltime : Accessor VMState_ι_ltime :=  {  acc := ·6  }   . 
Global Instance Acc_VMState_ι_code : Accessor VMState_ι_code :=  {  acc := ·7  }   . 
Global Instance Acc_VMState_ι_events : Accessor VMState_ι_events :=  {  acc := ·8  }   . 
Global Instance Acc_VMState_ι_savedDePoolContract : Accessor VMState_ι_savedDePoolContracts :=  {  acc := ·9  }   . 
Global Instance Acc_VMState_ι_msg_sender : Accessor VMState_ι_msg_sender :=  {  acc := ·10  }   . 
Global Instance Acc_VMState_ι_msg_value : Accessor VMState_ι_msg_value :=  {  acc := ·11  }   . 
Global Instance Acc_VMState_ι_messages : Accessor VMState_ι_messages :=  {  acc := ·12  }   .
Global Instance Acc_VMState_ι_msg_data : Accessor VMState_ι_msg_data :=  {  acc := ·13  }   .
Global Instance Acc_VMState_ι_transactions : Accessor VMState_ι_transactions :=  {  acc := ·14  }   .

Global Instance Acc_VMState_ι_accepted : Accessor VMState_ι_accepted :=  {  acc := ·15  }   .
Global Instance Acc_VMState_ι_reserved : Accessor VMState_ι_reserved :=  {  acc := ·16  }   .
Global Instance Acc_VMState_ι_currentCode : Accessor VMState_ι_currentCode :=  {  acc := ·17  }   .

Global Instance Acc_VMState_ι_validatorsElectedFor : Accessor VMState_ι_validatorsElectedFor :=  {  acc := ·18  }   .
Global Instance Acc_VMState_ι_electionsStartBefore : Accessor VMState_ι_electionsStartBefore :=  {  acc := ·19  }   .
Global Instance Acc_VMState_ι_electionsEndBefore : Accessor VMState_ι_electionsEndBefore :=  {  acc := ·20  }   .
Global Instance Acc_VMState_ι_stakeHeldFor : Accessor VMState_ι_stakeHeldFor :=  {  acc := ·21  }   .
	
Global Instance Acc_VMState_ι_curValidatorData : Accessor VMState_ι_curValidatorData :=  {  acc := ·22  }   .
Global Instance Acc_VMState_ι_unknown34 : Accessor VMState_ι_unknown34 :=  {  acc := ·23  }   .
Global Instance Acc_VMState_ι_utime_since : Accessor VMState_ι_utime_since :=  {  acc := ·24  }   .
Global Instance Acc_VMState_ι_utime_until : Accessor VMState_ι_utime_until :=  {  acc := ·25  }   .
	
Global Instance Acc_VMState_ι_prevValidatorData : Accessor VMState_ι_prevValidatorData :=  {  acc := ·26  }   .
	
Global Instance Acc_VMState_ι_rawConfigParam_17 : Accessor VMState_ι_rawConfigParam_17 :=  {  acc := ·27  }   .
Global Instance Acc_VMState_ι_unknown17_1 : Accessor VMState_ι_unknown17_1 :=  {  acc := ·28  }   .
Global Instance Acc_VMState_ι_unknown17_2 : Accessor VMState_ι_unknown17_2 :=  {  acc := ·29  }   .
Global Instance Acc_VMState_ι_unknown17_3 : Accessor VMState_ι_unknown17_3 :=  {  acc := ·30  }   .
Global Instance Acc_VMState_ι_maxStakeFactor : Accessor VMState_ι_maxStakeFactor :=  {  acc := ·31  }   .
	
Global Instance Acc_VMState_ι_rawConfigParam_1 : Accessor VMState_ι_rawConfigParam_1 :=  {  acc := ·32  }   .
Global Instance Acc_VMState_ι_electorRawAddress : Accessor VMState_ι_electorRawAddress :=  {  acc := ·33  }   .

Global Instance Acc_VMState_ι_deployed : Accessor VMState_ι_deployed :=  {  acc := ·34  }   .

Instance stateT_default {X}`{XDefault X} : XDefault (forall S, StateT S X) := 
  {default := fun S => state_unit (S:=S) default}.

Instance VMState_default : XDefault VMState :=  {  
	  default := VMStateC default default default default default default default 
							default default default default default default default 
							default default default default default default default
							default default default default default default default
							default default default default default default default
  }   . 

(* Print LocalStateP.  *)
Load "LocalStateInstances.v".
  
(*{I I8 I16 I32 I64 I128 I256 A B C S}%type_scope {L M HM P}%function_scope *)
Definition Ledger := @LedgerP XInteger  XInteger8 XInteger32 XInteger64 XInteger128 XInteger256 XAddress XBool TvmCell XString XList XMaybe XHMap XProd. 
Global Instance Struct_Ledger : Struct Ledger :=  { 
 	fields :=  [ 
 		@existT _ _ _ Ledger_ι_ValidatorBase , 
 		@existT _ _ _ Ledger_ι_ProxyBase , 
  		@existT _ _ _ Ledger_ι_ParticipantBase , 
 		@existT _ _ _ Ledger_ι_DePoolProxyContract , 
 		@existT _ _ _ Ledger_ι_RoundsBase , 
 		@existT _ _ _ Ledger_ι_DePoolContract , 
 		@existT _ _ _ Ledger_ι_VMState , 
 		@existT _ _ _ Ledger_ι_LocalState 
 	 ]   ;  
 	 ctor := LedgerC 
 }   . 
Global Instance Acc_Ledger_ι_ValidatorBase : Accessor Ledger_ι_ValidatorBase :=  {  acc := ·0  }   . 
Global Instance Acc_Ledger_ι_ProxyBase : Accessor Ledger_ι_ProxyBase :=  {  acc := ·1  }   . 
Global Instance Acc_Ledger_ι_ParticipantBase : Accessor Ledger_ι_ParticipantBase :=  {  acc := ·2  }   . 
Global Instance Acc_Ledger_ι_DePoolProxyContract : Accessor Ledger_ι_DePoolProxyContract :=  {  acc := ·3  }   . 
Global Instance Acc_Ledger_ι_RoundsBase : Accessor Ledger_ι_RoundsBase :=  {  acc := ·4  }   . 
Global Instance Acc_Ledger_ι_DePoolContract : Accessor Ledger_ι_DePoolContract :=  {  acc := ·5  }   . 
Global Instance Acc_Ledger_ι_VMState : Accessor Ledger_ι_VMState :=  {  acc := ·6  }   . 
Global Instance Acc_Ledger_ι_LocalState : Accessor Ledger_ι_LocalState :=  {  acc := ·7  }   . 
Instance Ledger_default : XDefault Ledger :=  {  
 	 default := LedgerC default default default default  
                        default default default default  
  }   . 
 Definition LedgerT := StateT Ledger .  

 
Global Instance AccAcc_ValidatorBase_ι_m_validatorWallet : AccessorAccessor ValidatorBase_ι_m_validatorWallet :=  {  accacc := Ledger_ι_ValidatorBase  }   . 

Global Instance AccAcc_ProxyBase_ι_m_proxies : AccessorAccessor ProxyBase_ι_m_proxies :=  {  accacc := Ledger_ι_ProxyBase  }   . 

Global Instance AccAcc_ParticipantBase_ι_m_participants : AccessorAccessor ParticipantBase_ι_m_participants :=  {  accacc := Ledger_ι_ParticipantBase  }   . 

Global Instance AccAcc_DePoolProxyContract_ι_m_dePool : AccessorAccessor DePoolProxyContract_ι_m_dePool :=                        {  accacc := Ledger_ι_DePoolProxyContract  }   . 

Global Instance AccAcc_RoundsBase_ι_m_rounds : AccessorAccessor RoundsBase_ι_m_rounds :=      {  accacc := Ledger_ι_RoundsBase }   . 
Global Instance AccAcc_RoundsBase_ι_m_roundQty : AccessorAccessor RoundsBase_ι_m_roundQty :=  {  accacc := Ledger_ι_RoundsBase  }   . 
Global Instance AccAcc_RoundsBase_ι_lastRoundInfo : AccessorAccessor RoundsBase_ι_lastRoundInfo := {  accacc := Ledger_ι_RoundsBase }   . 

Global Instance AccAcc_DePoolContract_ι_m_poolClosed : AccessorAccessor DePoolContract_ι_m_poolClosed :=                                       {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_m_minStake : AccessorAccessor DePoolContract_ι_m_minStake :=                                           {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_m_validatorAssurance : AccessorAccessor DePoolContract_ι_m_validatorAssurance :=                       {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_m_participantRewardFraction : AccessorAccessor DePoolContract_ι_m_participantRewardFraction :=         {  accacc := Ledger_ι_DePoolContract  }   . 

Global Instance AccAcc_DePoolContract_ι_m_validatorRewardFraction : AccessorAccessor DePoolContract_ι_m_validatorRewardFraction :=             {  accacc := Ledger_ι_DePoolContract  }   . 
Global Instance AccAcc_DePoolContract_ι_m_balanceThreshold : AccessorAccessor DePoolContract_ι_m_balanceThreshold :=                           {  accacc := Ledger_ι_DePoolContract  }   . 

Global Instance AccAcc_VMState_ι_pubkey : AccessorAccessor VMState_ι_pubkey :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_msg_pubkey : AccessorAccessor VMState_ι_msg_pubkey :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_now : AccessorAccessor VMState_ι_now :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_logstr : AccessorAccessor VMState_ι_logstr :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_balance : AccessorAccessor VMState_ι_balance :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_address : AccessorAccessor VMState_ι_address :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_ltime : AccessorAccessor VMState_ι_ltime :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_code : AccessorAccessor VMState_ι_code :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_events : AccessorAccessor VMState_ι_events :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_savedDePoolContract : AccessorAccessor VMState_ι_savedDePoolContracts :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_msg_sender : AccessorAccessor VMState_ι_msg_sender :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_msg_value : AccessorAccessor VMState_ι_msg_value :=  {  accacc := Ledger_ι_VMState  }   . 
Global Instance AccAcc_VMState_ι_messages : AccessorAccessor VMState_ι_messages :=  {  accacc := Ledger_ι_VMState  }   .
Global Instance AccAcc_VMState_ι_msg_data : AccessorAccessor VMState_ι_msg_data :=  {  accacc := Ledger_ι_VMState  }   .
Global Instance AccAcc_VMState_ι_transactions : AccessorAccessor VMState_ι_transactions :=  {  accacc := Ledger_ι_VMState  }   .
Global Instance AccAcc_VMState_ι_accepted : AccessorAccessor VMState_ι_accepted :=  {  accacc := Ledger_ι_VMState  }   .
Global Instance AccAcc_VMState_ι_reserved : AccessorAccessor VMState_ι_reserved :=  {  accacc := Ledger_ι_VMState  }   .
Global Instance AccAcc_VMState_ι_currentCode : AccessorAccessor VMState_ι_currentCode :=  {  accacc := Ledger_ι_VMState  }   .

Global Instance AccAcc_VMState_ι_validatorsElectedFor : AccessorAccessor VMState_ι_validatorsElectedFor :=   {  accacc := Ledger_ι_VMState  }  .
Global Instance AccAcc_VMState_ι_electionsStartBefore : AccessorAccessor VMState_ι_electionsStartBefore :=  {  accacc := Ledger_ι_VMState  }   .
Global Instance AccAcc_VMState_ι_electionsEndBefore : AccessorAccessor VMState_ι_electionsEndBefore :=   {  accacc := Ledger_ι_VMState  }   .
Global Instance AccAcc_VMState_ι_stakeHeldFor : AccessorAccessor VMState_ι_stakeHeldFor :=   {  accacc := Ledger_ι_VMState  }   .
	
Global Instance AccAcc_VMState_ι_curValidatorData : AccessorAccessor VMState_ι_curValidatorData :=   {  accacc := Ledger_ι_VMState  }   .
Global Instance AccAcc_VMState_ι_unknown34 : AccessorAccessor VMState_ι_unknown34 :=   {  accacc := Ledger_ι_VMState  }   .
Global Instance AccAcc_VMState_ι_utime_since : AccessorAccessor VMState_ι_utime_since :=   {  accacc := Ledger_ι_VMState  }   .
Global Instance AccAcc_VMState_ι_utime_until : AccessorAccessor VMState_ι_utime_until :=   {  accacc := Ledger_ι_VMState  }   .
	
Global Instance AccAcc_VMState_ι_prevValidatorData : AccessorAccessor VMState_ι_prevValidatorData :=   {  accacc := Ledger_ι_VMState  }   .
	
Global Instance AccAcc_VMState_ι_rawConfigParam_17 : AccessorAccessor VMState_ι_rawConfigParam_17 :=   {  accacc := Ledger_ι_VMState  }   .
Global Instance AccAcc_VMState_ι_unknown17_1 : AccessorAccessor VMState_ι_unknown17_1 :=   {  accacc := Ledger_ι_VMState  }  .
Global Instance AccAcc_VMState_ι_unknown17_2 : AccessorAccessor VMState_ι_unknown17_2 :=   {  accacc := Ledger_ι_VMState  }  .
Global Instance AccAcc_VMState_ι_unknown17_3 : AccessorAccessor VMState_ι_unknown17_3 :=   {  accacc := Ledger_ι_VMState  }   .
Global Instance AccAcc_VMState_ι_maxStakeFactor : AccessorAccessor VMState_ι_maxStakeFactor :=   {  accacc := Ledger_ι_VMState  }   .
	
Global Instance AccAcc_VMState_ι_rawConfigParam_1 : AccessorAccessor VMState_ι_rawConfigParam_1 :=   {  accacc := Ledger_ι_VMState  }   .
Global Instance AccAcc_VMState_ι_electorRawAddress : AccessorAccessor VMState_ι_electorRawAddress :=   {  accacc := Ledger_ι_VMState  }   .

Global Instance AccAcc_VMState_ι_deployed : AccessorAccessor VMState_ι_deployed :=   {  accacc := Ledger_ι_VMState  }   .

Global Instance AccAcc_LocalState_ι__addStakes_Л_participant  : AccessorAccessor LocalState_ι__addStakes_Л_participant :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__addStakes_Л_round   : AccessorAccessor LocalState_ι__addStakes_Л_round :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__addStakes_Л_sv  : AccessorAccessor LocalState_ι__addStakes_Л_sv :=  {  accacc := Ledger_ι_LocalState  }   . 

Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue :=  {  accacc := Ledger_ι_LocalState  }   .  
Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_newLock  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_newLock :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_newStake  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_newStake :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_newVesting   : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_newVesting :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_participant  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_participant :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_reward  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_reward :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_round0  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_round0 :=  {  accacc := Ledger_ι_LocalState  }   . 

Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_round2  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_round2 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvestForParticipant_Л_params  : AccessorAccessor LocalState_ι__returnOrReinvestForParticipant_Л_params :=  {  accacc := Ledger_ι_LocalState  }   . 


(* Global Instance AccAcc_LocalState_ι__returnOrReinvest_Л_chunkSize  : AccessorAccessor LocalState_ι__returnOrReinvest_Л_chunkSize :=  {  accacc := Ledger_ι_LocalState  }   .  *)
Global Instance AccAcc_LocalState_ι__returnOrReinvest_Л_round2  : AccessorAccessor LocalState_ι__returnOrReinvest_Л_round2 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvest_Л_round0   : AccessorAccessor LocalState_ι__returnOrReinvest_Л_round0 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι__returnOrReinvest_Л_startIndex  : AccessorAccessor LocalState_ι__returnOrReinvest_Л_startIndex :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_addVestingOrLock_Л_participant  : AccessorAccessor LocalState_ι_addVestingOrLock_Л_participant :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_addVestingOrLock_Л_l  : AccessorAccessor LocalState_ι_addVestingOrLock_Л_l :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_addVestingOrLock_Л_v  : AccessorAccessor LocalState_ι_addVestingOrLock_Л_v :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_completeRound_Л_i  : AccessorAccessor LocalState_ι_completeRound_Л_i :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_completeRound_Л_msgQty  : AccessorAccessor LocalState_ι_completeRound_Л_msgQty :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_completeRound_Л_restParticipant   : AccessorAccessor LocalState_ι_completeRound_Л_restParticipant :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_cutWithdrawalValue_Л_p  : AccessorAccessor LocalState_ι_cutWithdrawalValue_Л_p :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_cutWithdrawalValue_Л_withdrawal  : AccessorAccessor LocalState_ι_cutWithdrawalValue_Л_withdrawal :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_getRounds_Л_pair  : AccessorAccessor LocalState_ι_getRounds_Л_pair :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_getRounds_Л_rounds  : AccessorAccessor LocalState_ι_getRounds_Л_rounds :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_onFailToRecoverStake_Л_round  : AccessorAccessor LocalState_ι_onFailToRecoverStake_Л_round :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_onSuccessToRecoverStake_Л_round  : AccessorAccessor LocalState_ι_onSuccessToRecoverStake_Л_round :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_terminator_Л_round1  : AccessorAccessor LocalState_ι_terminator_Л_round1 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake  : AccessorAccessor LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStakeInOneRound_Л_destinationParticipant  : AccessorAccessor LocalState_ι_transferStakeInOneRound_Л_destinationParticipant :=  {  accacc := Ledger_ι_LocalState }   . 
Global Instance AccAcc_LocalState_ι_transferStakeInOneRound_Л_newSourceStake  : AccessorAccessor LocalState_ι_transferStakeInOneRound_Л_newSourceStake :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStakeInOneRound_Л_round  : AccessorAccessor LocalState_ι_transferStakeInOneRound_Л_round :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStakeInOneRound_Л_sourceParticipant  : AccessorAccessor LocalState_ι_transferStakeInOneRound_Л_sourceParticipant :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStakeInOneRound_Л_sourceStake  : AccessorAccessor LocalState_ι_transferStakeInOneRound_Л_sourceStake :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStake_Л_destParticipant  : AccessorAccessor LocalState_ι_transferStake_Л_destParticipant :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStake_Л_pair   : AccessorAccessor LocalState_ι_transferStake_Л_pair :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStake_Л_rounds  : AccessorAccessor LocalState_ι_transferStake_Л_rounds :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStake_Л_srcParticipant  : AccessorAccessor LocalState_ι_transferStake_Л_srcParticipant :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStake_Л_totalSrcStake  : AccessorAccessor LocalState_ι_transferStake_Л_totalSrcStake :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_transferStake_Л_transferred  : AccessorAccessor LocalState_ι_transferStake_Л_transferred :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_updateRound2_Л_round2  : AccessorAccessor LocalState_ι_updateRound2_Л_round2 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_updateRounds_Л_round0  : AccessorAccessor LocalState_ι_updateRounds_Л_round0 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_updateRounds_Л_round1  : AccessorAccessor LocalState_ι_updateRounds_Л_round1 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_updateRounds_Л_round2  : AccessorAccessor LocalState_ι_updateRounds_Л_round2 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_updateRounds_Л_roundPre0 : AccessorAccessor LocalState_ι_updateRounds_Л_roundPre0 :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_withdrawStakeInPoolingRound_Л_participant  : AccessorAccessor LocalState_ι_withdrawStakeInPoolingRound_Л_participant :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_withdrawStakeInPoolingRound_Л_round  : AccessorAccessor LocalState_ι_withdrawStakeInPoolingRound_Л_round :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_withdrawStakeInPoolingRound_Л_sv  : AccessorAccessor LocalState_ι_withdrawStakeInPoolingRound_Л_sv :=  {  accacc := Ledger_ι_LocalState  }   . 
Global Instance AccAcc_LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount  : AccessorAccessor LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount := {  accacc := Ledger_ι_LocalState  } .

Global Instance AccAcc_LocalState_ι_cutWithdrawalValue_Л_withdrawalTons  : AccessorAccessor LocalState_ι_cutWithdrawalValue_Л_withdrawalTons := {  accacc := Ledger_ι_LocalState  } .
Global Instance AccAcc_LocalState_ι_cutWithdrawalValue_Л_tonsForOwner  : AccessorAccessor LocalState_ι_cutWithdrawalValue_Л_tonsForOwner := {  accacc := Ledger_ι_LocalState  } .

Global Instance AccAcc_LocalState_ι_constructor6_Л_proxy : AccessorAccessor LocalState_ι_constructor6_Л_proxy := {  accacc := Ledger_ι_LocalState  } .

Global Instance AccAcc_LocalState_ι_totalParticipantFunds_Л_stakes : AccessorAccessor LocalState_ι_totalParticipantFunds_Л_stakes := {  accacc := Ledger_ι_LocalState  } .
Global Instance AccAcc_LocalState_ι_totalParticipantFunds_Л_pair : AccessorAccessor LocalState_ι_totalParticipantFunds_Л_pair := {  accacc := Ledger_ι_LocalState  } .




Instance DeployableContract_default : XDefault DeployableContract :=
{default := NullContractD}.

(* Print depoolContract.SolidityNotations.XBoolEquable. *)

Instance DeployableContract_equable : XBoolEquable XBool DeployableContract :=
{eqb := fun dc1 dc2 => match dc1, dc2 with
		| NullContractD, NullContractD => xBoolTrue
		| DePoolProxyContractD, DePoolProxyContractD => xBoolTrue
		| DePoolContractD, DePoolContractD => xBoolTrue
		| _, _ => xBoolFalse
        end } .


(* 1 *)
(*embeddedType for all Accessors *)


Unset Implicit Arguments.
Set Strict Implicit.
Unset Contextual Implicit.
Unset Maximal Implicit Insertion.

Definition projEmbed_Accessor {U T}{f: T -> U}`{s: Struct T}`{a: @Accessor T U s f}: T -> U := f.
Definition injEmbed_Accessor {U T}{f: T -> U}`{s: Struct T}`{a: @Accessor T U s f} (x: U) (t: T): T := {$ t with f := x $}.

 
 Definition T2 := ValidatorBase . 
 Definition T3 := ProxyBase . 
 Definition T5 := ParticipantBase . 
 Definition T10 := DePoolProxyContract .  
 Definition T11 := RoundsBase . 
 Definition T12 := DePoolContract . 
 Definition T16 := VMState . 
 Definition T17 := LocalState . 

  
 Definition projEmbed_T2 : Ledger -> T2 := projEmbed_Accessor . 
 Definition injEmbed_T2 : T2 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T2 : forall ( t : T2 ) ( s : Ledger ) , 
 projEmbed_T2 ( injEmbed_T2 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T2 : forall ( s : Ledger ) , injEmbed_T2 ( projEmbed_T2 s ) s = s . 
Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T2 : forall ( t1 t2 : T2 ) ( s : Ledger ) , 
 injEmbed_T2 t1 ( injEmbed_T2 t2 s) = 
 injEmbed_T2 t1 s . 
Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT2 : EmbeddedType Ledger T2 := 
 {
 projEmbed := projEmbed_T2 ; 
 injEmbed := injEmbed_T2 ; 
 projinj := projinj_T2 ; 
 injproj := injproj_T2 ; 
 injinj  := injinj_T2 ; 
 } . 
 
 Definition projEmbed_T3 : Ledger -> T3 := projEmbed_Accessor . 
 Definition injEmbed_T3 : T3 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T3 : forall ( t : T3 ) ( s : Ledger ) , 
 projEmbed_T3 ( injEmbed_T3 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T3 : forall ( s : Ledger ) , injEmbed_T3 ( projEmbed_T3 s ) s = s . 
Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T3 : forall ( t1 t2 : T3 ) ( s : Ledger ) , 
 injEmbed_T3 t1 ( injEmbed_T3 t2 s) = 
 injEmbed_T3 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT3 : EmbeddedType Ledger T3 := 
 {
 projEmbed := projEmbed_T3 ; 
 injEmbed := injEmbed_T3 ; 
 projinj := projinj_T3 ; 
 injproj := injproj_T3 ; 
 injinj  := injinj_T3 ; 
 } . 
 
 Definition projEmbed_T5 : Ledger -> T5 := projEmbed_Accessor . 
 Definition injEmbed_T5 : T5 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T5 : forall ( t : T5 ) ( s : Ledger ) , 
 projEmbed_T5 ( injEmbed_T5 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T5 : forall ( s : Ledger ) , injEmbed_T5 ( projEmbed_T5 s ) s = s . 
Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T5 : forall ( t1 t2 : T5 ) ( s : Ledger ) , 
 injEmbed_T5 t1 ( injEmbed_T5 t2 s) = 
 injEmbed_T5 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT5 : EmbeddedType Ledger T5 := 
 {
 projEmbed := projEmbed_T5 ; 
 injEmbed := injEmbed_T5 ; 
 projinj := projinj_T5 ; 
 injproj := injproj_T5 ; 
 injinj  := injinj_T5 ; 
 } . 
 
 Definition projEmbed_T10 : Ledger -> T10 := projEmbed_Accessor . 
 Definition injEmbed_T10 : T10 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T10 : forall ( t : T10 ) ( s : Ledger ) , 
 projEmbed_T10 ( injEmbed_T10 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T10 : forall ( s : Ledger ) , injEmbed_T10 ( projEmbed_T10 s ) s = s . 
Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T10 : forall ( t1 t2 : T10 ) ( s : Ledger ) , 
 injEmbed_T10 t1 ( injEmbed_T10 t2 s) = 
 injEmbed_T10 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT10 : EmbeddedType Ledger T10 := 
 {
 projEmbed := projEmbed_T10 ; 
 injEmbed := injEmbed_T10 ; 
 projinj := projinj_T10 ; 
 injproj := injproj_T10 ; 
 injinj  := injinj_T10 ; 
 } . 
 
 
 
 Definition projEmbed_T11 : Ledger -> T11 := projEmbed_Accessor . 
 Definition injEmbed_T11 : T11 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T11 : forall ( t : T11 ) ( s : Ledger ) , 
 projEmbed_T11 ( injEmbed_T11 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T11 : forall ( s : Ledger ) , injEmbed_T11 ( projEmbed_T11 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T11 : forall ( t1 t2 : T11 ) ( s : Ledger ) , 
 injEmbed_T11 t1 ( injEmbed_T11 t2 s) = 
 injEmbed_T11 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT11 : EmbeddedType Ledger T11 := 
 {
 projEmbed := projEmbed_T11 ; 
 injEmbed := injEmbed_T11 ; 
 projinj := projinj_T11 ; 
 injproj := injproj_T11 ; 
 injinj  := injinj_T11 ; 
 } . 
 
 Definition projEmbed_T12 : Ledger -> T12 := projEmbed_Accessor . 
 Definition injEmbed_T12 : T12 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T12 : forall ( t : T12 ) ( s : Ledger ) , 
 projEmbed_T12 ( injEmbed_T12 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T12 : forall ( s : Ledger ) , injEmbed_T12 ( projEmbed_T12 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T12 : forall ( t1 t2 : T12 ) ( s : Ledger ) , 
 injEmbed_T12 t1 ( injEmbed_T12 t2 s) = 
 injEmbed_T12 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT12 : EmbeddedType Ledger T12 := 
 {
 projEmbed := projEmbed_T12 ; 
 injEmbed := injEmbed_T12 ; 
 projinj := projinj_T12 ; 
 injproj := injproj_T12 ; 
 injinj  := injinj_T12 ; 
 } . 
 
 Definition projEmbed_T16 : Ledger -> T16 := projEmbed_Accessor . 
 Definition injEmbed_T16 : T16 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T16 : forall ( t : T16 ) ( s : Ledger ) , 
 projEmbed_T16 ( injEmbed_T16 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T16 : forall ( s : Ledger ) , injEmbed_T16 ( projEmbed_T16 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T16 : forall ( t1 t2 : T16 ) ( s : Ledger ) , 
 injEmbed_T16 t1 ( injEmbed_T16 t2 s) = 
 injEmbed_T16 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT16 : EmbeddedType Ledger T16 := 
 {
 projEmbed := projEmbed_T16 ; 
 injEmbed := injEmbed_T16 ; 
 projinj := projinj_T16 ; 
 injproj := injproj_T16 ; 
 injinj  := injinj_T16 ; 
 } . 
  
 Definition projEmbed_T17 : Ledger -> T17 := projEmbed_Accessor . 
 Definition injEmbed_T17 : T17 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T17 : forall ( t : T17 ) ( s : Ledger ) , 
 projEmbed_T17 ( injEmbed_T17 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T17 : forall ( s : Ledger ) , injEmbed_T17 ( projEmbed_T17 s ) s = s . 
Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T17 : forall ( t1 t2 : T17 ) ( s : Ledger ) , 
 injEmbed_T17 t1 ( injEmbed_T17 t2 s) = 
 injEmbed_T17 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT17 : EmbeddedType Ledger T17 := 
 {
 projEmbed := projEmbed_T17 ; 
 injEmbed := injEmbed_T17 ; 
 projinj := projinj_T17 ; 
 injproj := injproj_T17 ; 
 injinj  := injinj_T17 ; 
 } . 
 
Lemma injcommute_T2_T3: 
               forall ( u : T3 ) ( t : T2  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T2_T3 : 
@InjectCommutableStates Ledger (  T2  ) T3 := 
{
  injcommute := injcommute_T2_T3 
}.

Definition embeddedProduct_T2_T3 := 
           @embeddedProduct Ledger ( T2  ) T3
  
           InjectCommutableStates_T2_T3.

Existing Instance embeddedProduct_T2_T3 .
 
 
Lemma injcommute_T2xT3_T5: 
               forall ( u : T5 ) ( t : T2 * T3 ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T2xT3_T5 : 
@InjectCommutableStates Ledger ( T2 * T3 ) T5 := 
{
  injcommute := injcommute_T2xT3_T5 
}.

Definition embeddedProduct_T2xT3_T5 := 
           @embeddedProduct Ledger (  T2 * T3 ) T5
  
           InjectCommutableStates_T2xT3_T5.

Existing Instance embeddedProduct_T2xT3_T5 .
 
Lemma injcommute_T2xT3xT5_T10: 
               forall ( u : T10 ) ( t :  T2 * T3 * T5  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T2xT3xT5_T10 : 
@InjectCommutableStates Ledger (  T2 * T3 * T5 ) T10 := 
{
  injcommute := injcommute_T2xT3xT5_T10 
}.

Definition embeddedProduct_T2xT3xT5_T10 := 
           @embeddedProduct Ledger (  T2 * T3 * T5 ) T10
  
           InjectCommutableStates_T2xT3xT5_T10.

Existing Instance embeddedProduct_T2xT3xT5_T10 .
 
Lemma injcommute_T2xT3xT5xT10_T11: 
               forall ( u : T11 ) ( t :  T2 * T3 * T5 * T10  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T2xT3xT5xT10_T11 : 
@InjectCommutableStates Ledger ( T2 * T3 * T5 * T10  ) T11 := 
{
  injcommute := injcommute_T2xT3xT5xT10_T11 
}.

Definition embeddedProduct_T2xT3xT5xT10_T11 := 
           @embeddedProduct Ledger (  T2 * T3 * T5 * T10  ) T11
  
           InjectCommutableStates_T2xT3xT5xT10_T11.

Existing Instance embeddedProduct_T2xT3xT5xT10_T11 .
 
Lemma injcommute_T2xT3xT5xT10xT11_T12: 
               forall ( u : T12 ) ( t :  T2 * T3 * T5 * T10 * T11  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T2xT3xT5xT10xT11_T12 : 
@InjectCommutableStates Ledger (  T2 * T3 * T5 * T10 * T11  ) T12 := 
{
  injcommute := injcommute_T2xT3xT5xT10xT11_T12 
}.

Definition embeddedProduct_T2xT3xT5xT10xT11_T12 := 
           @embeddedProduct Ledger (  T2 * T3 * T5 * T10 * T11  ) T12
  
           InjectCommutableStates_T2xT3xT5xT10xT11_T12.

Existing Instance embeddedProduct_T2xT3xT5xT10xT11_T12 .

(* Print  injEmbed. *)
 
(* Print projEmbed. *)
Definition projEmbed_VMCommitted (l: Ledger) :  VMCommitted := 
	let p := projEmbed (EmbeddedType:=embeddedProduct_T2xT3xT5xT10xT11_T12) l in
	{| 
	VMCommitted_ι_ValidatorBase :=     ( fst ∘ fst ∘ fst ∘ fst ∘ fst ) p ; 
	VMCommitted_ι_ProxyBase :=         ( snd ∘ fst ∘ fst ∘ fst ∘ fst ) p ; 
	VMCommitted_ι_ParticipantBase :=   ( snd ∘ fst ∘ fst ∘ fst ) p ; 
    VMCommitted_ι_DePoolProxyContract:=( snd ∘ fst ∘ fst ) p ; 
	VMCommitted_ι_RoundsBase :=        ( snd ∘ fst ) p ; 
	VMCommitted_ι_DePoolContract :=      snd p ; 
	|}.

Definition injEmbed_VMCommitted (v : VMCommitted) (l: Ledger):  Ledger :=
	injEmbed (
         EmbeddedType:=embeddedProduct_T2xT3xT5xT10xT11_T12) 
			  ( VMCommitted_ι_ValidatorBase v,
			    VMCommitted_ι_ProxyBase v, 
			    VMCommitted_ι_ParticipantBase v, 
                VMCommitted_ι_DePoolProxyContract v,
			    VMCommitted_ι_RoundsBase v, 
                VMCommitted_ι_DePoolContract v
 ) l.
 
 Lemma projinj_VMCommitted : forall ( t : VMCommitted ) ( s : Ledger ) , 
 projEmbed_VMCommitted ( injEmbed_VMCommitted t s ) = t . 
 Proof.
 intros. compute. destruct t. auto.
Qed. 
 
 Lemma injproj_VMCommitted : forall ( s : Ledger ) , injEmbed_VMCommitted ( projEmbed_VMCommitted s ) s = s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 

 Lemma injinj_VMCommitted : forall ( t1 t2 : VMCommitted ) ( s : Ledger ) , 
 injEmbed_VMCommitted t1 ( injEmbed_VMCommitted t2 s) = 
 injEmbed_VMCommitted t1 s . 
 Proof.
 intros. destruct s. compute. destruct t1. auto.
Qed. 
 
 Instance embedded_VMCommitted : EmbeddedType Ledger VMCommitted := 
 {
 projEmbed := projEmbed_VMCommitted ; 
 injEmbed := injEmbed_VMCommitted ; 
 projinj := projinj_VMCommitted ; 
 injproj := injproj_VMCommitted ; 
 injinj  := injinj_VMCommitted ; 
 } .


Lemma injcommute_T2xT3xT5xT10xT11xT12_T16: 
               forall ( u : T16 ) ( t : T2 * T3 * T5 * T10 * T11 * T12 ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T2xT3xT5xT10xT11xT12_T16 : 
@InjectCommutableStates Ledger ( T2 * T3 * T5 * T10 * T11 * T12 ) T16 := 
{
  injcommute := injcommute_T2xT3xT5xT10xT11xT12_T16 
}.

Definition embeddedProduct_T2xT3xT5xT10xT11xT12_T16 := 
           @embeddedProduct Ledger (  T2 * T3 * T5 * T10 * T11 * T12 ) T16
  
           InjectCommutableStates_T2xT3xT5xT10xT11xT12_T16.

Existing Instance embeddedProduct_T2xT3xT5xT10xT11xT12_T16 .
 
Lemma injcommute_T2xT3xT5xT10xT11xT12xT16_T17: 
               forall ( u : T17 ) ( t : T2 * T3 * T5 * T10 * T11 * T12 * T16 ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T2xT3xT5xT10xT11xT12xT16_T17 : 
@InjectCommutableStates Ledger ( T2 * T3 * T5 * T10 * T11 * T12 * T16 ) T17 := 
{
  injcommute := injcommute_T2xT3xT5xT10xT11xT12xT16_T17 
}.

Definition embeddedProduct_T2xT3xT5xT10xT11xT12xT16_T17 := 
           @embeddedProduct Ledger ( T2 * T3 * T5 * T10 * T11 * T12 * T16 ) T17
  
           InjectCommutableStates_T2xT3xT5xT10xT11xT12xT16_T17.

Existing Instance embeddedProduct_T2xT3xT5xT10xT11xT12xT16_T17 .
 
Lemma fullState_T2xT3xT5xT10xT11xT12xT16_T17 : forall s s0, 
      injEmbed ( T:=( T2 * T3 * T5 * T10 * T11 * T12 * T16  ) ) 
(projEmbed s) (injEmbed (T:= T17 ) (projEmbed s) s0) = s.
Proof.
  intros. compute. destruct s.
  auto.
Qed. 

Instance FullState_T2xT3xT5xT10xT11xT12xT16_T17 : 
         FullState Ledger ( T2 * T3 * T5 * T10 * T11 * T12 * T16  ) T17 := 
{
  injComm := InjectCommutableStates_T2xT3xT5xT10xT11xT12xT16_T17 ;
  fullState := fullState_T2xT3xT5xT10xT11xT12xT16_T17 
}. 

(* Print liftEmbeddedState. *)

Notation "'↑ε17' m":= (liftEmbeddedState ( H := embeddedT17 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε16' m":= (liftEmbeddedState ( H := embeddedT16 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope.  
Notation "'↑ε12' m":= (liftEmbeddedState ( H := embeddedT12 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε11' m":= (liftEmbeddedState ( H := embeddedT11 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε10' m":= (liftEmbeddedState ( H := embeddedT10 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε5' m":= (liftEmbeddedState ( H := embeddedT5 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε3' m":= (liftEmbeddedState ( H := embeddedT3 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 
Notation "'↑ε2' m":= (liftEmbeddedState ( H := embeddedT2 ) ( ε m )%sol ) (at level 10, left associativity): solidity_scope. 

Notation "'↑17' m":= (liftEmbeddedState ( H := embeddedT17 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑16' m":= (liftEmbeddedState ( H := embeddedT16 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑12' m":= (liftEmbeddedState ( H := embeddedT12 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑11' m":= (liftEmbeddedState ( H := embeddedT11 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑10' m":= (liftEmbeddedState ( H := embeddedT10 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑5' m":= (liftEmbeddedState ( H := embeddedT5 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑3' m":= (liftEmbeddedState ( H := embeddedT3 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑2' m":= (liftEmbeddedState ( H := embeddedT2 ) ( m ) ) (at level 10, left associativity): solidity_scope. 
Notation "'↑0' m " := ( liftEmbeddedState ( H :=  embeddedProduct_T2xT3xT5xT10xT11xT12_T16 ) ( m )) (at level 10, left associativity): solidity_scope. 
 
Notation "'↑↑17'":= (liftEmbeddedState ( H := embeddedT17 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑16'":= (liftEmbeddedState ( H := embeddedT16 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑12'":= (liftEmbeddedState ( H := embeddedT12 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑11'":= (liftEmbeddedState ( H := embeddedT11 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑10'":= (liftEmbeddedState ( H := embeddedT10 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑5'":= (liftEmbeddedState ( H := embeddedT5 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑3'":= (liftEmbeddedState ( H := embeddedT3 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑2'":= (liftEmbeddedState ( H := embeddedT2 )  ) (at level 32, left associativity): solidity_scope. 
Notation "'↑↑0'" := ( liftEmbeddedState ( H :=  embeddedProduct_T2xT3xT5xT10xT11xT12_T16 ) ) (at level 32, left associativity): solidity_scope. 

Parameter local0: LocalState.

(* Print callEmbeddedStateAdj. *)

Notation "↓ m" := (callEmbeddedStateAdj m local0 (H0 :=  FullState_T2xT3xT5xT10xT11xT12xT16_T17) ) (at level 31, left associativity): solidity_scope.

(* Notation " '↑↑1' n '^^' m " := ( do a ← (↑5 n  ) ; return! ( m a )  )%sol(at level 10, left associativity): solidity_scope.
Notation " '↑↑2' n '^^' m " := ( do a ← (↑11 n  ) ; return! ( m a )  )%sol(at level 10, left associativity): solidity_scope.
Notation " '↑↑3' n '^^' m " := ( do a ← (↑17 n  ) ; return! ( m a )  )%sol(at level 10, left associativity): solidity_scope.
Notation " '↑↑4' n '^^' m " := ( do a ← (↑17 n  ) ; return! ( m a )  )%sol(at level 10, left associativity): solidity_scope.
 *)

 Definition completionReasonEqb (cr1 cr2: RoundsBase_ι_CompletionReason) : XBool :=
	match cr1, cr2 with
	| RoundsBase_ι_CompletionReasonP_ι_Undefined, RoundsBase_ι_CompletionReasonP_ι_Undefined => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_PoolClosed, RoundsBase_ι_CompletionReasonP_ι_PoolClosed => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_FakeRound, RoundsBase_ι_CompletionReasonP_ι_FakeRound => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall, RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_StakeIsRejectedByElector, RoundsBase_ι_CompletionReasonP_ι_StakeIsRejectedByElector => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived, RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_ElectionsAreLost, RoundsBase_ι_CompletionReasonP_ι_ElectionsAreLost => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished, RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_NoValidatorRequest, RoundsBase_ι_CompletionReasonP_ι_NoValidatorRequest => xBoolTrue
	| RoundsBase_ι_CompletionReasonP_ι_BadProxy, RoundsBase_ι_CompletionReasonP_ι_BadProxy => xBoolTrue
	| _, _ => xBoolFalse
	end.

Global Instance completionReasonEquable: XBoolEquable XBool RoundsBase_ι_CompletionReason	:= { eqb:= completionReasonEqb }.


Definition completionReason2XInteger (cr: RoundsBase_ι_CompletionReason) : XInteger := 
	match cr with
	| RoundsBase_ι_CompletionReasonP_ι_Undefined => xInt0
	| RoundsBase_ι_CompletionReasonP_ι_PoolClosed => xInt1
	| RoundsBase_ι_CompletionReasonP_ι_FakeRound => xInt2
	| RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall => xInt3
	| RoundsBase_ι_CompletionReasonP_ι_StakeIsRejectedByElector => xInt4
	| RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived => xInt5
	| RoundsBase_ι_CompletionReasonP_ι_ElectionsAreLost => xInt6
	| RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished => xInt7
	| RoundsBase_ι_CompletionReasonP_ι_NoValidatorRequest => xInt8
	| RoundsBase_ι_CompletionReasonP_ι_BadProxy => xInt9
	end	.

Global Instance completionReasonIntegerable : XIntegerable XInteger RoundsBase_ι_CompletionReason :=
 { toInteger := completionReason2XInteger }.
	
Definition roundStepEqb (cr1 cr2: RoundsBase_ι_RoundStep) : XBool :=
	match cr1, cr2 with
	| RoundsBase_ι_RoundStepP_ι_Pooling, RoundsBase_ι_RoundStepP_ι_Pooling => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest, RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted, RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_WaitingValidationStart, RoundsBase_ι_RoundStepP_ι_WaitingValidationStart => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections, RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze, RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_WaitingReward, RoundsBase_ι_RoundStepP_ι_WaitingReward => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_Completing, RoundsBase_ι_RoundStepP_ι_Completing => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_Completed, RoundsBase_ι_RoundStepP_ι_Completed => xBoolTrue
	| RoundsBase_ι_RoundStepP_ι_PrePooling, RoundsBase_ι_RoundStepP_ι_PrePooling => xBoolTrue
	| _, _ => xBoolFalse
	end.

Global Instance roudStepEquable: XBoolEquable XBool RoundsBase_ι_RoundStep	:= { eqb:= roundStepEqb }.

Definition eventEqb (e1 e2: LedgerEvent): XBool := xBoolFalse.

End LedgerClass .
