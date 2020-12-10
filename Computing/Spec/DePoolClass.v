
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import FinProof.ProgrammingWith.

Local Open Scope record.
Local Open Scope program_scope. 

Require Import FinProof.Common.
Require Import FinProof.StateMonad2.
Require Import depoolContract.SolidityNotations.

Inductive LedgerEventP  := NoEvent.
Definition LedgerEvent := LedgerEventP.


Inductive RoundsBase_ι_RoundStepP := 
 | RoundsBase_ι_RoundStepP_ι_Pooling : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingValidatorRequest : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingIfStakeAccepted : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingValidationStart : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingIfValidatorWinElections : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingUnfreeze : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_WaitingReward : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_Completing : RoundsBase_ι_RoundStepP 
 | RoundsBase_ι_RoundStepP_ι_Completed : RoundsBase_ι_RoundStepP . 
 
 Inductive RoundsBase_ι_CompletionReasonP := 
 | RoundsBase_ι_CompletionReasonP_ι_Undefined : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_PoolClosed : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_FakeRound : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_TotalStakeIsTooSmall : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_ValidatorStakeIsTooSmall : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_StakeIsRejectedByElector : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_RewardIsReceived : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_ElectionsAreLost : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_ValidatorIsPunished : RoundsBase_ι_CompletionReasonP 
 | RoundsBase_ι_CompletionReasonP_ι_NoValidatorRequest : RoundsBase_ι_CompletionReasonP . 
 
 Instance RoundsBase_ι_RoundStepP_default : XDefault RoundsBase_ι_RoundStepP := { 
 default := RoundsBase_ι_RoundStepP_ι_Pooling } . 
 
 Instance RoundsBase_ι_CompletionReasonP_default : XDefault RoundsBase_ι_CompletionReasonP := { 
 default := RoundsBase_ι_CompletionReasonP_ι_Undefined } . 
 
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
  Record DebugDePoolP { I32 }  := DebugDePoolC  { 
 	DebugDePool_ι_validators_elected_for : I32  ;   (* constant := 18_000  ;  *) 
 	DebugDePool_ι_elections_start_before : I32  ;   (* constant := 9_000  ;  *) 
 	DebugDePool_ι_elections_end_before : I32  ;   (* constant := 2_000  ;  *) 
 	DebugDePool_ι_stake_held_for : I32  ;   (* constant := 9_000  ;  *) 
 
 }   . 
 
 Arguments DebugDePoolC  [  I32  ]   . 
  Record ValidatorBaseP { A }  := ValidatorBaseC  { 
 	ValidatorBase_ι_m_validatorWallet : A  
 
 }   . 
 
 Arguments ValidatorBaseC  [  A  ]   . 

Record DePoolLib_ι_ParticipantP  {  I8 I64 B  }  := DePoolLib_ι_ParticipantC  { 
 	DePoolLib_ι_Participant_ι_roundQty : I8  ;  
 	DePoolLib_ι_Participant_ι_reward : I64  ;  
 	DePoolLib_ι_Participant_ι_haveVesting : B  ;  
 	DePoolLib_ι_Participant_ι_haveLock : B  ;  
 	DePoolLib_ι_Participant_ι_reinvest : B  ;  
 	DePoolLib_ι_Participant_ι_withdrawValue : I64   
  }  .  
 
 
 Arguments DePoolLib_ι_ParticipantC  [  I8 I64 B  ]   . 




   Record ParticipantBaseP { HM : Type->Type->Type } { A I8 I64 B }  := ParticipantBaseC  { 
 	ParticipantBase_ι_m_participants : HM A (@ DePoolLib_ι_ParticipantP I8 I64 B )  
 } . 
 
 Arguments ParticipantBaseC  [ HM A I8 I64 B ] 
 
 
   . 
 Record DePoolHelperP { I A }  := DePoolHelperC  { 
 	DePoolHelper_ι_TICKTOCK_FEE : I  ;   (* constant := 1e9  ;  *) 
 	DePoolHelper_ι_TIMER_FEE : I  ;   (* constant := 1e9  ;  *) 
 	DePoolHelper_ι_m_dePoolPool : A  ; 
 
 	DePoolHelper_ι_m_timer : A  ; 
 	DePoolHelper_ι_m_timeout : I  
 
 }   . 
 
 Arguments DePoolHelperC  [  I A  ]   . 
 Record ErrorsP { I }  := ErrorsC  { 
 	Errors_ι_IS_NOT_OWNER : I  ;   (* constant := 101  ;  *) 
 	Errors_ι_NOT_ENOUGH_FUNDS : I  ;   (* constant := 105  ;  *) 
 	Errors_ι_IS_NOT_OWNER2 : I  ;   (* constant := 106  ;  *) 
 	Errors_ι_IS_NOT_PROXY : I  ;   (* constant := 107  ;  *) 
 	Errors_ι_IS_EXT_MSG : I  ;   (* constant := 108  ;  *) 
 	Errors_ι_INVALID_ELECTION_ID : I  ;   (* constant := 111  ;  *) 
 	Errors_ι_REPEATED_REQUEST : I  ;   (* constant := 112  ;  *) 
 	Errors_ι_IS_NOT_VALIDATOR : I  ;   (* constant := 113  ;  *) 
 	Errors_ι_DEPOOL_IS_CLOSED : I  ;   (* constant := 114  ;  *) 
 	Errors_ι_NO_SUCH_PARTICIPANT : I  ;   (* constant := 116  ;  *) 
 	Errors_ι_WRONG_ROUND_STATE : I  ;   (* constant := 118  ;  *) 
 	Errors_ι_INVALID_ADDRESS : I  ;   (* constant := 119  ;  *) 
 	Errors_ι_IS_NOT_DEPOOL : I  ;   (* constant := 120  ;  *) 
 	Errors_ι_NO_PENDING_ROUNDS : I  ;   (* constant := 121  ;  *) 
 	Errors_ι_PENDING_ROUND_IS_TOO_YOUNG : I  ;   (* constant := 122  ;  *) 
 	Errors_ι_TRANSFER_IS_FORBIDDEN : I  ;   (* constant := 123  ;  *) 
 	Errors_ι_NO_ELECTION_ROUND : I  ;   (* constant := 124  ;  *) 
 	Errors_ι_INVALID_ROUND_STEP : I  ;   (* constant := 125  ;  *) 
 	Errors_ι_INVALID_QUERY_ID : I  ;   (* constant := 126  ;  *) 
 	Errors_ι_IS_NOT_ELECTOR : I  ;   (* constant := 127  ;  *) 
 }   . 
 
 Arguments ErrorsC  [  I  ]   . 
 Record InternalErrorsP { I }  := InternalErrorsC  { 
 	InternalErrors_ι_ERROR507 : I  ;   (* constant := 507  ;  *) 
 	InternalErrors_ι_ERROR508 : I  ;   (* constant := 508  ;  *) 
 	InternalErrors_ι_ERROR509 : I  ;   (* constant := 509  ;  *) 
 	InternalErrors_ι_ERROR511 : I  ;   (* constant := 511  ;  *) 
 	InternalErrors_ι_ERROR513 : I  ;   (* constant := 513  ;  *) 
 	InternalErrors_ι_ERROR516 : I  ;   (* constant := 516  ;  *) 
 	InternalErrors_ι_ERROR517 : I  ;   (* constant := 517  ;  *) 
 	InternalErrors_ι_ERROR518 : I  ;   (* constant := 518  ;  *) 
 	InternalErrors_ι_ERROR519 : I  ;   (* constant := 519  ;  *) 
 	InternalErrors_ι_ERROR521 : I  ;   (* constant := 521  ;  *) 
 	InternalErrors_ι_ERROR522 : I  ;   (* constant := 522  ;  *) 
 	InternalErrors_ι_ERROR523 : I  ;   (* constant := 523  ;  *) 
 }   . 
 
 Arguments InternalErrorsC  [  I  ]   . 
 


 Record DePoolLib_ι_RequestP  {  I64 I256 I32 I8  }  := DePoolLib_ι_RequestC  { 
 	DePoolLib_ι_Request_ι_queryId : I64  ;  
 	DePoolLib_ι_Request_ι_validatorKey : I256  ;  
 	DePoolLib_ι_Request_ι_stakeAt : I32  ;  
 	DePoolLib_ι_Request_ι_maxFactor : I32  ;  
 	DePoolLib_ι_Request_ι_adnlAddr : I256  ;  
 	DePoolLib_ι_Request_ι_signature : I8   
  }  .  
 
 
 Arguments DePoolLib_ι_RequestC  [  I64 I256 I32 I8  ]   . 
 Record DePoolLibP { I64 I32 }  := DePoolLibC  { 
 	DePoolLib_ι_PROXY_FEE : I64  ;   (* constant := 0  .  09 ton  ;  *) 
 	DePoolLib_ι_ELECTOR_FEE : I64  ;   (* constant := 1 ton  ;  *) 
 	DePoolLib_ι_MAX_UINT64 : I64  ;   (* constant := 0xFFFF_FFFF_FFFF_FFFF  ;  *) 
 	DePoolLib_ι_MAX_TIME : I32  ;   (* constant := 0xFFFF_FFFF  ;  *) 
 	DePoolLib_ι_ELECTOR_UNFREEZE_LAG : I64  ;   (* constant := 1 minutes  ;  *) 
 }   . 
 
 Arguments DePoolLibC  [  I64 I32  ]   . 
 Record DePoolProxyContractP { A }  := DePoolProxyContractC  { 
 	DePoolProxyContract_ι_m_dePool : A  
 
 }   . 
 
 Arguments DePoolProxyContractC  [  A  ]   . 
 Record RoundsBase_ι_InvestParamsP  {  B I64 I32 A  }  := RoundsBase_ι_InvestParamsC  { 
 	RoundsBase_ι_InvestParams_ι_isActive : B  ;  
 	RoundsBase_ι_InvestParams_ι_amount : I64  ;  
 	RoundsBase_ι_InvestParams_ι_lastWithdrawalTime : I64  ;  
 	RoundsBase_ι_InvestParams_ι_withdrawalPeriod : I32  ;  
 	RoundsBase_ι_InvestParams_ι_withdrawalValue : I64  ;  
 	RoundsBase_ι_InvestParams_ι_owner : A   
  }  .  
 
 
 Arguments RoundsBase_ι_InvestParamsC  [  B I64 I32 A  ]   . 
 Record RoundsBase_ι_StakeValueP  {  I64  }  := RoundsBase_ι_StakeValueC  { 
 	RoundsBase_ι_StakeValue_ι_ordinary : I64   
    }  .  
 
 
 Arguments RoundsBase_ι_StakeValueC  [  I64  ]   . 
 Record RoundsBase_ι_RoundP { I64 I32 } { HM : Type->Type->Type } { A I256 }  := RoundsBase_ι_RoundC  { 
 	RoundsBase_ι_Round_ι_id : I64  ;  
 	RoundsBase_ι_Round_ι_supposedElectedAt : I32  ;  
 	RoundsBase_ι_Round_ι_unfreeze : I32  ;  
 	RoundsBase_ι_Round_ι_step : (@ RoundsBase_ι_RoundStepP )  ;  
 	RoundsBase_ι_Round_ι_completionReason : (@ RoundsBase_ι_CompletionReasonP )  ;  
 	RoundsBase_ι_Round_ι_participantQty : I32  ;  
 	RoundsBase_ι_Round_ι_stake : I64  ;  
 	RoundsBase_ι_Round_ι_stakes : HM A (@ RoundsBase_ι_StakeValueP I64 )  ;  
 	RoundsBase_ι_Round_ι_rewards : I64  ;  
  	RoundsBase_ι_Round_ι_elector : A  ;  
 	RoundsBase_ι_Round_ι_vsetHashInElectionPhase : I256  ;  
 	RoundsBase_ι_Round_ι_proxy : A  ;  
 	RoundsBase_ι_Round_ι_start : I32  ;  
 	RoundsBase_ι_Round_ι_end : I32  ;  
 	RoundsBase_ι_Round_ι_unused : I64   
  } . 
 
 Arguments RoundsBase_ι_RoundC  [ I64 I32 HM A I256 ] 
 
 
   . 
 Record RoundsBase_ι_TruncatedRoundP { I64 I32 I256 }  := RoundsBase_ι_TruncatedRoundC  { 
 	RoundsBase_ι_TruncatedRound_ι_id : I64  ;  
 	RoundsBase_ι_TruncatedRound_ι_supposedElectedAt : I32  ;  
 	RoundsBase_ι_TruncatedRound_ι_unfreeze : I32  ;  
 	RoundsBase_ι_TruncatedRound_ι_step : (@ RoundsBase_ι_RoundStepP )  ;  
 	RoundsBase_ι_TruncatedRound_ι_completionReason : (@ RoundsBase_ι_CompletionReasonP )  ;  
 	RoundsBase_ι_TruncatedRound_ι_participantQty : I32  ;  
 	RoundsBase_ι_TruncatedRound_ι_stake : I64  ;  
 	RoundsBase_ι_TruncatedRound_ι_rewards : I64  ;  
 	RoundsBase_ι_TruncatedRound_ι_unused : I64  ;  
 	RoundsBase_ι_TruncatedRound_ι_start : I64  ;  
 	RoundsBase_ι_TruncatedRound_ι_end : I64  ;  
 	RoundsBase_ι_TruncatedRound_ι_vsetHash : I256   
  } . 
 
 Arguments RoundsBase_ι_TruncatedRoundC  [ I64 I32 I256 ] 
 
 
   . 
 Record DePoolContractP { I8 I64 I16 B }  := DePoolContractC  { 
 	DePoolContract_ι_PART_FRACTION : I8  ;   (* constant := 70  ;  *) 
 	DePoolContract_ι_VALIDATOR_FRACTION : I8  ;   (* constant := 25  ;  *) 
 	DePoolContract_ι_VALIDATOR_WALLET_MIN_STAKE : I8  ;   (* constant := 20  ;  *) 
 	DePoolContract_ι_ADD_STAKE_FEE : I64  ;   (* constant := 50 milliton  ;  *) 
 	DePoolContract_ι_ADD_VESTING_OR_LOCK_FEE : I64  ;   (* constant := 80 milliton  ;  *) 
 	DePoolContract_ι_REMOVE_ORDINARY_STAKE_FEE : I64  ;   (* constant := 50 milliton  ;  *) 
 	DePoolContract_ι_WITHDRAW_PART_AFTER_COMPLETING_FEE : I64  ;   (* constant := 25 milliton  ;  *) 
 	DePoolContract_ι_WITHDRAW_ALL_AFTER_COMPLETING_FEE : I64  ;   (* constant := 30 milliton  ;  *) 
 	DePoolContract_ι_TRANSFER_STAKE_FEE : I64  ;   (* constant := 135 milliton  ;  *) 
 	DePoolContract_ι_RET_OR_REINV_FEE : I64  ;   (* constant := 50 milliton  ;  *) 
 	DePoolContract_ι_ANSWER_MSG_FEE : I64  ;   (* constant := 3 milliton  ;  *) 
 	DePoolContract_ι_MAX_MSGS_PER_TR : I8  ;   (* constant := 25  ;  *) 
 	DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS : I16  ;   (* constant := 250  ;  *) 
 
 	DePoolContract_ι_VALUE_FOR_SELF_CALL : I64  ;   (* constant := 1 ton  ;  *) 
 	DePoolContract_ι_STATUS_SUCCESS : I8  ;   (* constant := 0  ;  *) 
 	DePoolContract_ι_STATUS_STAKE_TOO_SMALL : I8  ;   (* constant := 1  ;  *) 
 	DePoolContract_ι_STATUS_DEPOOL_CLOSED : I8  ;   (* constant := 3  ;  *) 
 	DePoolContract_ι_STATUS_ROUND_STAKE_LIMIT : I8  ;   (* constant := 4  ;  *) 
 	DePoolContract_ι_STATUS_MSG_VAL_TOO_SMALL : I8  ;   (* constant := 5  ;  *) 
 	DePoolContract_ι_STATUS_NO_PARTICIPANT : I8  ;   (* constant := 6  ;  *) 
 	DePoolContract_ι_STATUS_NO_TRANSFER_WHILE_PENDING_ROUND : I8  ;   (* constant := 8  ;  *) 
 	DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_VESTING : I8  ;   (* constant := 9  ;  *) 
 	DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD : I8  ;   (* constant := 10  ;  *) 
 	DePoolContract_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS : I8  ;   (* constant := 11  ;  *) 
 	DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO : I8  ;   (* constant := 12  ;  *) 
 	DePoolContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD : I8  ;   (* constant := 13  ;  *) 
 	DePoolContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO : I8  ;   (* constant := 14  ;  *) 
 	DePoolContract_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL : I8  ;   (* constant := 16  ;  *) 
 	DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_LOCK : I8  ;   (* constant := 17  ;  *) 
 	DePoolContract_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG : I8  ;   (* constant := 18  ;  *) 
 	DePoolContract_ι_STATUS_TRANSFER_SELF : I8  ;   (* constant := 19  ;  *) 
 	DePoolContract_ι_m_poolClosed : B  ; 
 	DePoolContract_ι_m_minStake : I64  ; 
 	DePoolContract_ι_m_minRoundStake : I64  ; 
 	DePoolContract_ι_m_lastRoundInterest : I64  
 
 
 
 
 
 
 }   . 
 
 Arguments DePoolContractC  [  I8 I64 I16 B  ]   . 
    Record TestElector_ι_ValidatorP  {  I64 I256 I32 I8  }  := TestElector_ι_ValidatorC  { 
 	TestElector_ι_Validator_ι_stake : I64  ;  
 	TestElector_ι_Validator_ι_key : I256  ;  
 	TestElector_ι_Validator_ι_reward : I64  ;  
 	TestElector_ι_Validator_ι_qid : I64  ;  
 	TestElector_ι_Validator_ι_factor : I32  ;  
 	TestElector_ι_Validator_ι_adnl : I256  ;  
 	TestElector_ι_Validator_ι_signature : I8   
  }  .  
 
 
 Arguments TestElector_ι_ValidatorC  [  I64 I256 I32 I8  ]   . 
 Record TestElectorP { HM : Type->Type->Type } { I32 I256 I64 I8 }  := TestElectorC  { 
 	TestElector_ι_elections : HM I256 (@ TestElector_ι_ValidatorP I64 I256 I32 I8 )  ; 
 	TestElector_ι_electAt : I32  ; 
 	TestElector_ι_ELECTIONS_BEGIN_BEFORE : I32  ;   (* constant := 12  ;  *) 
 	TestElector_ι_ELECTIONS_END_BEFORE : I32  ;   (* constant := 6  ;  *) 
 	TestElector_ι_ELECTED_FOR : I32  ;   (* constant := 24  ;  *) 
 	TestElector_ι_STAKE_HELD_FOR : I32  ;   (* constant := 12  ;  *) 
 
 } . 
 
 Arguments TestElectorC  [ HM I32 I256 I64 I8 ] 
 
 
   . 
 Record VMStateP { I256 I64 S I128 C } { L : Type->Type } { I8 I16 B }  := VMStateC  { 
 	VMState_ι_pubkey : I256  ; 
 	VMState_ι_msg_pubkey : I256  ; 
 	VMState_ι_now : I64  ; 
 	VMState_ι_logstr : S  ; 
 	VMState_ι_balance : I128  ; 
 	VMState_ι_address : I256  ; 
 	VMState_ι_ltime : I256  ; 
 	VMState_ι_code : C  ; 
 VMState_ι_events : L (@ LedgerEventP )  ;   (* LedgerEvent *) 
 	VMState_ι_savedDePoolContract : (@ DePoolContractP I8 I64 I16 B )  
 } . 
 
 Arguments VMStateC  [ I256 I64 S I128 C L I8 I16 B ] 
 
 
   . 
 Record LocalStateP { I I64 A C B I256 I32 I8 I128 I16 } { HM : Type->Type->Type }  := LocalStateC  { 
 	LocalState_ι_getCurValidatorData_Л_t : I  ; 
 	LocalState_ι_getPrevValidatorHash_Л_t : I  ; 
 	LocalState_ι_getProxy_Л_roundId : I64  ; 
 	LocalState_ι__recoverStake_Л_proxy : A  ; 
 	LocalState_ι__recoverStake_Л_requestId : I64  ; 
 	LocalState_ι__recoverStake_Л_elector : A  ; 
 	LocalState_ι__sendElectionRequest_Л_proxy : A  ; 
 	LocalState_ι__sendElectionRequest_Л_requestId : I64  ; 
 	LocalState_ι__sendElectionRequest_Л_validatorStake : I64  ; 
 	LocalState_ι__sendElectionRequest_Л_elector : A  ; 
 	LocalState_ι_getCurValidatorData_Л_cell : C  ; 
 	LocalState_ι_getPrevValidatorHash_Л_cell : C  ; 
 	LocalState_ι_roundTimeParams_Л_ok : B  ; 
 	LocalState_ι_getMaxStakeFactor_Л_cell : C  ; 
 	LocalState_ι_getElector_Л_cell : C  ; 
 	LocalState_ι_getOrCreateParticipant_Л_addr : A  ; 
 	LocalState_ι__setOrDeleteParticipant_Л_addr : A  ; 
 	LocalState_ι_setTimer_Л_timer : I  ; 
 	LocalState_ι_updateDePoolPoolAddress_Л_addr : A  ; 
 	LocalState_ι_initTimer_Л_timer : A  ; 
 	LocalState_ι_initTimer_Л_period : I  ; 
 	LocalState_ι__settimer_Л_timer : A  ; 
 	LocalState_ι__settimer_Л_period : I  ; 
 	LocalState_ι_onTimer_Л_timer : A  ; 
 	LocalState_ι_upgrade_Л_newcode : C  ; 
 	LocalState_ι_process_new_stake_Л_queryId : I64  ; 
 	LocalState_ι_process_new_stake_Л_validatorKey : I256  ; 
 	LocalState_ι_process_new_stake_Л_stakeAt : I32  ; 
 	LocalState_ι_process_new_stake_Л_maxFactor : I32  ; 
 	LocalState_ι_process_new_stake_Л_adnlAddr : I256  ; 
 	LocalState_ι_process_new_stake_Л_signature : I8  ; 
 	LocalState_ι_process_new_stake_Л_elector : A  ; 
 	LocalState_ι_onStakeAccept_Л_queryId : I64  ; 
 	LocalState_ι_onStakeAccept_Л_comment : I32  ; 
 	LocalState_ι_onStakeReject_Л_queryId : I64  ; 
 	LocalState_ι_onStakeReject_Л_comment : I32  ; 
 	LocalState_ι_recover_stake_Л_queryId : I64  ; 
 	LocalState_ι_recover_stake_Л_elector : A  ; 
 	LocalState_ι_onSuccessToRecoverStake_Л_queryId : I64  ; 
 	LocalState_ι__addStakes_Л_round : (@ RoundsBase_ι_RoundP I64 I32 HM A I256 )  ; 
 	LocalState_ι__addStakes_Л_participantAddress : A  ; 
 	LocalState_ι__addStakes_Л_stake : I64  ; 
 	LocalState_ι__addStakes_Л_vesting : (@ RoundsBase_ι_InvestParamsP B I64 I32 A )  ; 
 	LocalState_ι__addStakes_Л_lock : (@ RoundsBase_ι_InvestParamsP B I64 I32 A )  ; 
 	LocalState_ι_transferStakeInOneRound_Л_round : (@ RoundsBase_ι_RoundP I64 I32 HM A I256 )  ; 
 	LocalState_ι_transferStakeInOneRound_Л_source : A  ; 
 	LocalState_ι_transferStakeInOneRound_Л_destination : A  ; 
 	LocalState_ι_transferStakeInOneRound_Л_amount : I64  ; 
 	LocalState_ι_transferStakeInOneRound_Л_minStake : I64  ; 
 	LocalState_ι_withdrawStakeInPoolingRound_Л_participantAddress : A  ; 
 	LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount : I64  ; 
 	LocalState_ι_withdrawStakeInPoolingRound_Л_minStake : I64  ; 
 	LocalState_ι_withdrawStakeInPoolingRound_Л_round : (@ RoundsBase_ι_RoundP I64 I32 HM A I256 )  ; 
 	LocalState_ι_sumOfStakes_Л_stakes : (@ RoundsBase_ι_StakeValueP I64 )  ; 
 	LocalState_ι_toTruncatedRound_Л_round : (@ RoundsBase_ι_RoundP I64 I32 HM A I256 )  ; 
 	LocalState_ι__calcLastRoundInterest_Л_totalStake : I64  ; 
 	LocalState_ι__calcLastRoundInterest_Л_rewards : I64  ; 
 	LocalState_ι__sendError_Л_errcode : I32  ; 
 	LocalState_ι__sendError_Л_comment : I64  ; 
 	LocalState_ι__sendAccept_Л_fee : I64  ; 
 	LocalState_ι_startRoundCompleting_Л_round : (@ RoundsBase_ι_RoundP I64 I32 HM A I256 )  ; 
 	LocalState_ι_startRoundCompleting_Л_reason : (@ RoundsBase_ι_CompletionReasonP )  ; 
 	LocalState_ι_cutWithdrawalValue_Л_p : (@ RoundsBase_ι_InvestParamsP B I64 I32 A )  ; 
 	LocalState_ι_cutWithdrawalValue_Л_periodQty : I64  ; 
 	LocalState_ι__returnOrReinvestForParticipant_Л_completedRound : (@ RoundsBase_ι_RoundP I64 I32 HM A I256 )  ; 
 	LocalState_ι__returnOrReinvestForParticipant_Л_round0 : (@ RoundsBase_ι_RoundP I64 I32 HM A I256 )  ; 
 	LocalState_ι__returnOrReinvestForParticipant_Л_addr : A  ; 
 	LocalState_ι__returnOrReinvestForParticipant_Л_stakes : (@ RoundsBase_ι_StakeValueP I64 )  ; 
 	LocalState_ι__returnOrReinvestForParticipant_Л_validatorIsPunished : B  ; 
 	LocalState_ι__returnOrReinvest_Л_round : (@ RoundsBase_ι_RoundP I64 I32 HM A I256 )  ; 
 	LocalState_ι__returnOrReinvest_Л_chunkSize : I8  ; 
 	LocalState_ι_calculateStakeWithAssert_Л_doSplit : B  ; 
 	LocalState_ι_calculateStakeWithAssert_Л_wholeFee : I64  ; 
 	LocalState_ι_calculateStakeWithAssert_Л_div : I64  ; 
 	LocalState_ι_addOrdinaryStake_Л_reinvest : B  ; 
 	LocalState_ι_removeOrdinaryStake_Л_withdrawValue : I64  ; 
 	LocalState_ι_addVestingStake_Л_beneficiary : A  ; 
 	LocalState_ι_addVestingStake_Л_withdrawalPeriod : I32  ; 
 	LocalState_ι_addVestingStake_Л_totalPeriod : I32  ; 
 	LocalState_ι_addLockStake_Л_beneficiary : A  ; 
 	LocalState_ι_addLockStake_Л_withdrawalPeriod : I32  ; 
 	LocalState_ι_addLockStake_Л_totalPeriod : I32  ; 
 	LocalState_ι_addVestingOrLock_Л_beneficiary : A  ; 
 	LocalState_ι_addVestingOrLock_Л_withdrawalPeriod : I32  ; 
 	LocalState_ι_addVestingOrLock_Л_totalPeriod : I32  ; 
 	LocalState_ι_addVestingOrLock_Л_isVesting : B  ; 
 	LocalState_ι_withdrawPartAfterCompleting_Л_withdrawValue : I64  ; 
 	LocalState_ι_withdrawAllAfterCompleting_Л_doWithdrawAll : B  ; 
 	LocalState_ι_transferStake_Л_dest : A  ; 
 	LocalState_ι_transferStake_Л_amount : I64  ; 
 	LocalState_ι_participateInElections_Л_queryId : I64  ; 
 	LocalState_ι_participateInElections_Л_validatorKey : I256  ; 
 	LocalState_ι_participateInElections_Л_stakeAt : I32  ; 
 	LocalState_ι_participateInElections_Л_maxFactor : I32  ; 
 	LocalState_ι_participateInElections_Л_adnlAddr : I256  ; 
 	LocalState_ι_participateInElections_Л_signature : I8  ; 
 	LocalState_ι_participateInElections_Л_WaitingValidatorRequest : (@ RoundsBase_ι_RoundStepP )  ; 
 	LocalState_ι_generateRound_Л_MAX_TIME : (@ DePoolLibP I64 I32 )  ; 
 	LocalState_ι_generateRound_Л_Pooling : (@ RoundsBase_ι_RoundStepP )  ; 
 	LocalState_ι_generateRound_Л_Undefined : (@ RoundsBase_ι_CompletionReasonP )  ; 
 	LocalState_ι_updateRound2_Л_round2 : (@ RoundsBase_ι_RoundP I64 I32 HM A I256 )  ; 
 	LocalState_ι_updateRound2_Л_prevValidatorHash : I256  ; 
 	LocalState_ι_updateRound2_Л_curValidatorHash : I256  ; 
 	LocalState_ι_updateRound2_Л_validationStart : I32  ; 
 	LocalState_ι_updateRound2_Л_stakeHeldFor : I32  ; 
 	LocalState_ι_updateRounds_Л_validationStart : I32  ; 
 	LocalState_ι_completeRoundWithChunk_Л_roundId : I64  ; 
 	LocalState_ι_completeRoundWithChunk_Л_chunkSize : I8  ; 
 	LocalState_ι_completeRoundWithChunk_Л_Completing : (@ RoundsBase_ι_RoundStepP )  ; 
 	LocalState_ι_completeRound_Л_roundId : I64  ; 
 	LocalState_ι_completeRound_Л_participantQty : I32  ; 
 	LocalState_ι_completeRound_Л_Completing : (@ RoundsBase_ι_RoundStepP )  ; 
 	LocalState_ι_onStakeAccept_Л_elector : A  ; 
 	LocalState_ι_onStakeAccept_Л_WaitingIfStakeAccepted : (@ RoundsBase_ι_RoundStepP )  ; 
 	LocalState_ι_onStakeReject_Л_elector : A  ; 
 	LocalState_ι_onStakeReject_Л_WaitingIfStakeAccepted : (@ RoundsBase_ι_RoundStepP )  ; 
 	LocalState_ι_acceptRewardAndStartRoundCompleting_Л_round : (@ RoundsBase_ι_RoundP I64 I32 HM A I256 )  ; 
 	LocalState_ι_acceptRewardAndStartRoundCompleting_Л_value : I64  ; 
 	LocalState_ι_acceptRewardAndStartRoundCompleting_Л_effectiveStake : I64  ; 
 	LocalState_ι_onSuccessToRecoverStake_Л_elector : A  ; 
 	LocalState_ι_onFailToRecoverStake_Л_queryId : I64  ; 
 	LocalState_ι_onFailToRecoverStake_Л_elector : A  ; 
 	LocalState_ι_getParticipantInfo_Л_addr : A  ; 
 	LocalState_ι_onRoundComplete_Л_roundId : I64  ; 
 	LocalState_ι_onRoundComplete_Л_reward : I64  ; 
 	LocalState_ι_onRoundComplete_Л_ordinaryStake : I64  ; 
 	LocalState_ι_onRoundComplete_Л_vestingStake : I64  ; 
 	LocalState_ι_onRoundComplete_Л_lockStake : I64  ; 
 	LocalState_ι_onRoundComplete_Л_reinvest : B  ; 
 	LocalState_ι_onRoundComplete_Л_reason : I8  ; 
 	LocalState_ι_receiveAnswer_Л_errcode : I32  ; 
 	LocalState_ι_receiveAnswer_Л_comment : I64  ; 
 	LocalState_ι_onTransfer_Л_source : A  ; 
 	LocalState_ι_onTransfer_Л_amount : I128  ; 
 	LocalState_ι_sendTransaction_Л_dest : A  ; 
 	LocalState_ι_sendTransaction_Л_value : I64  ; 
 	LocalState_ι_sendTransaction_Л_bounce : B  ; 
 	LocalState_ι_sendTransaction_Л_flags : I16  ; 
 	LocalState_ι_sendTransaction_Л_payload : C  ; 
 	LocalState_ι_acceptRecoveredStake_Л_queryId : I64  ; 
 	LocalState_ι_sendError_Л_queryId : I64  ; 
 	LocalState_ι_sendError_Л_op : I32  
 } . 
 
 Arguments LocalStateC  [ I I64 A C B I256 I32 I8 I128 I16 HM ] 
 
 
   . 
 Record LedgerP { I32 A } { HM : Type->Type->Type } { I8 I64 B I I16 I256 S I128 C } { L : Type->Type }  := LedgerC  { 
 	Ledger_ι_DebugDePool : (@ DebugDePoolP I32 )  ; 
 	Ledger_ι_AcceptBase : True  ; 
 	Ledger_ι_ValidatorBase : (@ ValidatorBaseP A )  ; 
 	Ledger_ι_ProxyBase : True  ; 
 	Ledger_ι_ConfigParamsBase : True  ; 
 	Ledger_ι_ParticipantBase : (@ ParticipantBaseP HM A I8 I64 B )  ; 
 	Ledger_ι_DePoolHelper : (@ DePoolHelperP I A )  ; 
 	Ledger_ι_Errors : (@ ErrorsP I )  ; 
 	Ledger_ι_InternalErrors : (@ InternalErrorsP I )  ; 
 	Ledger_ι_DePoolLib : (@ DePoolLibP I64 I32 )  ; 
 	Ledger_ι_DePoolProxyContract : (@ DePoolProxyContractP A )  ; 
 	Ledger_ι_RoundsBase : True  ; 
 	Ledger_ι_DePoolContract : (@ DePoolContractP I8 I64 I16 B )  ; 
 	Ledger_ι_DePool : True  ; 
 	Ledger_ι_Participant : True  ; 
 	Ledger_ι_TestElector : (@ TestElectorP HM I32 I256 I64 I8 )  ; 
 	Ledger_ι_VMState : (@ VMStateP I256 I64 S I128 C L I8 I16 B )  ; 
 	Ledger_ι_LocalState : (@ LocalStateP I I64 A C B I256 I32 I8 I128 I16 HM )  
 }   . 
 
 Arguments LedgerC [ I32 A HM I8 I64 B I I16 I256 S I128 C L ] . 
 
Module LedgerClass (xt: XTypesSig) (sm: StateMonadSig) .
Module SolidityNotations := SolidityNotations.SolidityNotations xt sm.
Import SolidityNotations.
Existing Instance monadStateT.
Existing Instance monadStateStateT.
  
  
 Definition DebugDePool := @DebugDePoolP XInteger32 . 
Global Instance Struct_DebugDePool : Struct DebugDePool :=  { 
 	fields :=  [ 
 		@existT _ _ _ DebugDePool_ι_validators_elected_for , 
 		@existT _ _ _ DebugDePool_ι_elections_start_before , 
 		@existT _ _ _ DebugDePool_ι_elections_end_before , 
 		@existT _ _ _ DebugDePool_ι_stake_held_for 
 
 	 ]   ;  
 	 ctor := @DebugDePoolC XInteger32 
 }   . 
Global Instance Acc_DebugDePool_ι_validators_elected_for : Accessor DebugDePool_ι_validators_elected_for :=  {  acc := ·0  }   . 
Global Instance Acc_DebugDePool_ι_elections_start_before : Accessor DebugDePool_ι_elections_start_before :=  {  acc := ·1  }   . 
Global Instance Acc_DebugDePool_ι_elections_end_before : Accessor DebugDePool_ι_elections_end_before :=  {  acc := ·2  }   . 
Global Instance Acc_DebugDePool_ι_stake_held_for : Accessor DebugDePool_ι_stake_held_for :=  {  acc := ·3  }   . 
Instance DebugDePool_default : XDefault DebugDePool :=  {  
 	 default := DebugDePoolC default default default default  
  }   . 
(* Definition DebugDePoolT := StateT DebugDePool . *) 
  
  
 Definition ValidatorBase := @ValidatorBaseP XAddress . 
Global Instance Struct_ValidatorBase : Struct ValidatorBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ ValidatorBase_ι_m_validatorWallet 
 
 	 ]   ;  
 	 ctor := @ValidatorBaseC XAddress 
 }   . 
Global Instance Acc_ValidatorBase_ι_m_validatorWallet : Accessor ValidatorBase_ι_m_validatorWallet :=  {  acc := ·0  }   . 
Instance ValidatorBase_default : XDefault ValidatorBase :=  {  
 	 default := ValidatorBaseC default  
  }   . 
(* Definition ValidatorBaseT := StateT ValidatorBase . *) 
   
  
 Definition ParticipantBase := @ParticipantBaseP XHMap XAddress XInteger8 XInteger64 XBool . 
Global Instance Struct_ParticipantBase : Struct ParticipantBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ ParticipantBase_ι_m_participants 
 	 ]   ;  
 	 ctor := @ParticipantBaseC XHMap XAddress XInteger8 XInteger64 XBool 
 }   . 
Global Instance Acc_ParticipantBase_ι_m_participants : Accessor ParticipantBase_ι_m_participants :=  {  acc := ·0  }   . 
Instance ParticipantBase_default : XDefault ParticipantBase :=  {  
 	 default := ParticipantBaseC default  
  }   . 
(* Definition ParticipantBaseT := StateT ParticipantBase . *) 
 
  
 Definition DePoolHelper := @DePoolHelperP XInteger XAddress . 
Global Instance Struct_DePoolHelper : Struct DePoolHelper :=  { 
 	fields :=  [ 
 		@existT _ _ _ DePoolHelper_ι_TICKTOCK_FEE , 
 		@existT _ _ _ DePoolHelper_ι_TIMER_FEE , 
 		@existT _ _ _ DePoolHelper_ι_m_dePoolPool , 
 
 		@existT _ _ _ DePoolHelper_ι_m_timer , 
 		@existT _ _ _ DePoolHelper_ι_m_timeout 
 
 	 ]   ;  
 	 ctor := @DePoolHelperC XInteger XAddress 
 }   . 
Global Instance Acc_DePoolHelper_ι_TICKTOCK_FEE : Accessor DePoolHelper_ι_TICKTOCK_FEE :=  {  acc := ·0  }   . 
Global Instance Acc_DePoolHelper_ι_TIMER_FEE : Accessor DePoolHelper_ι_TIMER_FEE :=  {  acc := ·1  }   . 
Global Instance Acc_DePoolHelper_ι_m_dePoolPool : Accessor DePoolHelper_ι_m_dePoolPool :=  {  acc := ·2  }   . 
Global Instance Acc_DePoolHelper_ι_m_timer : Accessor DePoolHelper_ι_m_timer :=  {  acc := ·3  }   . 
Global Instance Acc_DePoolHelper_ι_m_timeout : Accessor DePoolHelper_ι_m_timeout :=  {  acc := ·4  }   . 
Instance DePoolHelper_default : XDefault DePoolHelper :=  {  
 	 default := DePoolHelperC default default default default default  
  }   . 
(* Definition DePoolHelperT := StateT DePoolHelper . *) 
 
  
 Definition Errors := @ErrorsP XInteger . 
Global Instance Struct_Errors : Struct Errors :=  { 
 	fields :=  [ 
 		@existT _ _ _ Errors_ι_IS_NOT_OWNER , 
 		@existT _ _ _ Errors_ι_NOT_ENOUGH_FUNDS , 
 		@existT _ _ _ Errors_ι_IS_NOT_OWNER2 , 
 		@existT _ _ _ Errors_ι_IS_NOT_PROXY , 
 		@existT _ _ _ Errors_ι_IS_EXT_MSG , 
 		@existT _ _ _ Errors_ι_INVALID_ELECTION_ID , 
 		@existT _ _ _ Errors_ι_REPEATED_REQUEST , 
 		@existT _ _ _ Errors_ι_IS_NOT_VALIDATOR , 
 		@existT _ _ _ Errors_ι_DEPOOL_IS_CLOSED , 
 		@existT _ _ _ Errors_ι_NO_SUCH_PARTICIPANT , 
 		@existT _ _ _ Errors_ι_WRONG_ROUND_STATE , 
 		@existT _ _ _ Errors_ι_INVALID_ADDRESS , 
 		@existT _ _ _ Errors_ι_IS_NOT_DEPOOL , 
 		@existT _ _ _ Errors_ι_NO_PENDING_ROUNDS , 
 		@existT _ _ _ Errors_ι_PENDING_ROUND_IS_TOO_YOUNG , 
 		@existT _ _ _ Errors_ι_TRANSFER_IS_FORBIDDEN , 
 		@existT _ _ _ Errors_ι_NO_ELECTION_ROUND , 
 		@existT _ _ _ Errors_ι_INVALID_ROUND_STEP , 
 		@existT _ _ _ Errors_ι_INVALID_QUERY_ID , 
 		@existT _ _ _ Errors_ι_IS_NOT_ELECTOR 
 	 ]   ;  
 	 ctor := @ErrorsC XInteger 
 }   . 
Global Instance Acc_Errors_ι_IS_NOT_OWNER : Accessor Errors_ι_IS_NOT_OWNER :=  {  acc := ·0  }   . 
Global Instance Acc_Errors_ι_NOT_ENOUGH_FUNDS : Accessor Errors_ι_NOT_ENOUGH_FUNDS :=  {  acc := ·1  }   . 
Global Instance Acc_Errors_ι_IS_NOT_OWNER2 : Accessor Errors_ι_IS_NOT_OWNER2 :=  {  acc := ·2  }   . 
Global Instance Acc_Errors_ι_IS_NOT_PROXY : Accessor Errors_ι_IS_NOT_PROXY :=  {  acc := ·3  }   . 
Global Instance Acc_Errors_ι_IS_EXT_MSG : Accessor Errors_ι_IS_EXT_MSG :=  {  acc := ·4  }   . 
Global Instance Acc_Errors_ι_INVALID_ELECTION_ID : Accessor Errors_ι_INVALID_ELECTION_ID :=  {  acc := ·5  }   . 
Global Instance Acc_Errors_ι_REPEATED_REQUEST : Accessor Errors_ι_REPEATED_REQUEST :=  {  acc := ·6  }   . 
Global Instance Acc_Errors_ι_IS_NOT_VALIDATOR : Accessor Errors_ι_IS_NOT_VALIDATOR :=  {  acc := ·7  }   . 
Global Instance Acc_Errors_ι_DEPOOL_IS_CLOSED : Accessor Errors_ι_DEPOOL_IS_CLOSED :=  {  acc := ·8  }   . 
Global Instance Acc_Errors_ι_NO_SUCH_PARTICIPANT : Accessor Errors_ι_NO_SUCH_PARTICIPANT :=  {  acc := ·9  }   . 
Global Instance Acc_Errors_ι_WRONG_ROUND_STATE : Accessor Errors_ι_WRONG_ROUND_STATE :=  {  acc := ·10  }   . 
Global Instance Acc_Errors_ι_INVALID_ADDRESS : Accessor Errors_ι_INVALID_ADDRESS :=  {  acc := ·11  }   . 
Global Instance Acc_Errors_ι_IS_NOT_DEPOOL : Accessor Errors_ι_IS_NOT_DEPOOL :=  {  acc := ·12  }   . 
Global Instance Acc_Errors_ι_NO_PENDING_ROUNDS : Accessor Errors_ι_NO_PENDING_ROUNDS :=  {  acc := ·13  }   . 
Global Instance Acc_Errors_ι_PENDING_ROUND_IS_TOO_YOUNG : Accessor Errors_ι_PENDING_ROUND_IS_TOO_YOUNG :=  {  acc := ·14  }   . 
Global Instance Acc_Errors_ι_TRANSFER_IS_FORBIDDEN : Accessor Errors_ι_TRANSFER_IS_FORBIDDEN :=  {  acc := ·15  }   . 
Global Instance Acc_Errors_ι_NO_ELECTION_ROUND : Accessor Errors_ι_NO_ELECTION_ROUND :=  {  acc := ·16  }   . 
Global Instance Acc_Errors_ι_INVALID_ROUND_STEP : Accessor Errors_ι_INVALID_ROUND_STEP :=  {  acc := ·17  }   . 
Global Instance Acc_Errors_ι_INVALID_QUERY_ID : Accessor Errors_ι_INVALID_QUERY_ID :=  {  acc := ·18  }   . 
Global Instance Acc_Errors_ι_IS_NOT_ELECTOR : Accessor Errors_ι_IS_NOT_ELECTOR :=  {  acc := ·19  }   . 
Instance Errors_default : XDefault Errors :=  {  
 	 default := ErrorsC default default default default default default default default default default default default default default default default default default default default  
  }   . 
(* Definition ErrorsT := StateT Errors . *) 
 
  
 Definition InternalErrors := @InternalErrorsP XInteger . 
Global Instance Struct_InternalErrors : Struct InternalErrors :=  { 
 	fields :=  [ 
 		@existT _ _ _ InternalErrors_ι_ERROR507 , 
 		@existT _ _ _ InternalErrors_ι_ERROR508 , 
 		@existT _ _ _ InternalErrors_ι_ERROR509 , 
 		@existT _ _ _ InternalErrors_ι_ERROR511 , 
 		@existT _ _ _ InternalErrors_ι_ERROR513 , 
 		@existT _ _ _ InternalErrors_ι_ERROR516 , 
 		@existT _ _ _ InternalErrors_ι_ERROR517 , 
 		@existT _ _ _ InternalErrors_ι_ERROR518 , 
 		@existT _ _ _ InternalErrors_ι_ERROR519 , 
 		@existT _ _ _ InternalErrors_ι_ERROR521 , 
 		@existT _ _ _ InternalErrors_ι_ERROR522 , 
 		@existT _ _ _ InternalErrors_ι_ERROR523 
 	 ]   ;  
 	 ctor := @InternalErrorsC XInteger 
 }   . 
Global Instance Acc_InternalErrors_ι_ERROR507 : Accessor InternalErrors_ι_ERROR507 :=  {  acc := ·0  }   . 
Global Instance Acc_InternalErrors_ι_ERROR508 : Accessor InternalErrors_ι_ERROR508 :=  {  acc := ·1  }   . 
Global Instance Acc_InternalErrors_ι_ERROR509 : Accessor InternalErrors_ι_ERROR509 :=  {  acc := ·2  }   . 
Global Instance Acc_InternalErrors_ι_ERROR511 : Accessor InternalErrors_ι_ERROR511 :=  {  acc := ·3  }   . 
Global Instance Acc_InternalErrors_ι_ERROR513 : Accessor InternalErrors_ι_ERROR513 :=  {  acc := ·4  }   . 
Global Instance Acc_InternalErrors_ι_ERROR516 : Accessor InternalErrors_ι_ERROR516 :=  {  acc := ·5  }   . 
Global Instance Acc_InternalErrors_ι_ERROR517 : Accessor InternalErrors_ι_ERROR517 :=  {  acc := ·6  }   . 
Global Instance Acc_InternalErrors_ι_ERROR518 : Accessor InternalErrors_ι_ERROR518 :=  {  acc := ·7  }   . 
Global Instance Acc_InternalErrors_ι_ERROR519 : Accessor InternalErrors_ι_ERROR519 :=  {  acc := ·8  }   . 
Global Instance Acc_InternalErrors_ι_ERROR521 : Accessor InternalErrors_ι_ERROR521 :=  {  acc := ·9  }   . 
Global Instance Acc_InternalErrors_ι_ERROR522 : Accessor InternalErrors_ι_ERROR522 :=  {  acc := ·10  }   . 
Global Instance Acc_InternalErrors_ι_ERROR523 : Accessor InternalErrors_ι_ERROR523 :=  {  acc := ·11  }   . 
Instance InternalErrors_default : XDefault InternalErrors :=  {  
 	 default := InternalErrorsC default default default default default default default default default default default default  
  }   . 
(* Definition InternalErrorsT := StateT InternalErrors . *) 
 
  
 Definition DePoolLib_ι_Participant := @DePoolLib_ι_ParticipantP XInteger8 XInteger64 XBool . 
 Definition DePoolLib_ι_Request := @DePoolLib_ι_RequestP XInteger64 XInteger256 XInteger32 XInteger8 . 
 Definition DePoolLib := @DePoolLibP XInteger64 XInteger32 . 
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
 	 ctor := @DePoolLib_ι_ParticipantC XInteger8 XInteger64 XBool 
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
 	 ctor := @DePoolLib_ι_RequestC XInteger64 XInteger256 XInteger32 XInteger8 
 }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_queryId : Accessor DePoolLib_ι_Request_ι_queryId :=  {  acc := ·0  }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_validatorKey : Accessor DePoolLib_ι_Request_ι_validatorKey :=  {  acc := ·1  }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_stakeAt : Accessor DePoolLib_ι_Request_ι_stakeAt :=  {  acc := ·2  }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_maxFactor : Accessor DePoolLib_ι_Request_ι_maxFactor :=  {  acc := ·3  }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_adnlAddr : Accessor DePoolLib_ι_Request_ι_adnlAddr :=  {  acc := ·4  }   . 
Global Instance Acc_DePoolLib_ι_Request_ι_signature : Accessor DePoolLib_ι_Request_ι_signature :=  {  acc := ·5  }   . 
Global Instance Struct_DePoolLib : Struct DePoolLib :=  { 
 	fields :=  [ 
 		@existT _ _ _ DePoolLib_ι_PROXY_FEE , 
 		@existT _ _ _ DePoolLib_ι_ELECTOR_FEE , 
 		@existT _ _ _ DePoolLib_ι_MAX_UINT64 , 
 		@existT _ _ _ DePoolLib_ι_MAX_TIME , 
 		@existT _ _ _ DePoolLib_ι_ELECTOR_UNFREEZE_LAG 
 	 ]   ;  
 	 ctor := @DePoolLibC XInteger64 XInteger32 
 }   . 
Global Instance Acc_DePoolLib_ι_PROXY_FEE : Accessor DePoolLib_ι_PROXY_FEE :=  {  acc := ·0  }   . 
Global Instance Acc_DePoolLib_ι_ELECTOR_FEE : Accessor DePoolLib_ι_ELECTOR_FEE :=  {  acc := ·1  }   . 
Global Instance Acc_DePoolLib_ι_MAX_UINT64 : Accessor DePoolLib_ι_MAX_UINT64 :=  {  acc := ·2  }   . 
Global Instance Acc_DePoolLib_ι_MAX_TIME : Accessor DePoolLib_ι_MAX_TIME :=  {  acc := ·3  }   . 
Global Instance Acc_DePoolLib_ι_ELECTOR_UNFREEZE_LAG : Accessor DePoolLib_ι_ELECTOR_UNFREEZE_LAG :=  {  acc := ·4  }   . 
Instance DePoolLib_ι_Participant_default : XDefault DePoolLib_ι_Participant :=  {  
 	 default := DePoolLib_ι_ParticipantC default default default default default default  
  }   . 
Instance DePoolLib_ι_Request_default : XDefault DePoolLib_ι_Request :=  {  
 	 default := DePoolLib_ι_RequestC default default default default default default  
  }   . 
Instance DePoolLib_default : XDefault DePoolLib :=  {  
 	 default := DePoolLibC default default default default default  
  }   . 
(* Definition DePoolLibT := StateT DePoolLib . *) 
 
  
 Definition DePoolProxyContract := @DePoolProxyContractP XAddress . 
Global Instance Struct_DePoolProxyContract : Struct DePoolProxyContract :=  { 
 	fields :=  [ 
 		@existT _ _ _ DePoolProxyContract_ι_m_dePool 
 
 	 ]   ;  
 	 ctor := @DePoolProxyContractC XAddress 
 }   . 
Global Instance Acc_DePoolProxyContract_ι_m_dePool : Accessor DePoolProxyContract_ι_m_dePool :=  {  acc := ·0  }   . 
Instance DePoolProxyContract_default : XDefault DePoolProxyContract :=  {  
 	 default := DePoolProxyContractC default  
  }   . 
(* Definition DePoolProxyContractT := StateT DePoolProxyContract . *) 
 
  
 Definition RoundsBase_ι_InvestParams := @RoundsBase_ι_InvestParamsP XBool XInteger64 XInteger32 XAddress . 
 Definition RoundsBase_ι_StakeValue := @RoundsBase_ι_StakeValueP XInteger64 . 
 Definition RoundsBase_ι_Round := @RoundsBase_ι_RoundP XInteger64 XInteger32 XHMap XAddress XInteger256 . 
 Definition RoundsBase_ι_TruncatedRound := @RoundsBase_ι_TruncatedRoundP XInteger64 XInteger32 XInteger256 . 
 Bind Scope struct_scope with RoundsBase_ι_InvestParams  . 
 Bind Scope struct_scope with RoundsBase_ι_StakeValue  . 
 Bind Scope struct_scope with RoundsBase_ι_Round  . 
 Bind Scope struct_scope with RoundsBase_ι_TruncatedRound  . 
Global Instance Struct_RoundsBase_ι_InvestParams : Struct RoundsBase_ι_InvestParams :=  {  
 	 fields :=  [  
 		@existT _ _ _ RoundsBase_ι_InvestParams_ι_isActive , 
 		@existT _ _ _ RoundsBase_ι_InvestParams_ι_amount , 
 		@existT _ _ _ RoundsBase_ι_InvestParams_ι_lastWithdrawalTime , 
 		@existT _ _ _ RoundsBase_ι_InvestParams_ι_withdrawalPeriod , 
 		@existT _ _ _ RoundsBase_ι_InvestParams_ι_withdrawalValue , 
 		@existT _ _ _ RoundsBase_ι_InvestParams_ι_owner 
 	  ]   ;  
 	 ctor := @RoundsBase_ι_InvestParamsC XBool XInteger64 XInteger32 XAddress 
 }   . 
Global Instance Acc_RoundsBase_ι_InvestParams_ι_isActive : Accessor RoundsBase_ι_InvestParams_ι_isActive :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase_ι_InvestParams_ι_amount : Accessor RoundsBase_ι_InvestParams_ι_amount :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase_ι_InvestParams_ι_lastWithdrawalTime : Accessor RoundsBase_ι_InvestParams_ι_lastWithdrawalTime :=  {  acc := ·2  }   . 
Global Instance Acc_RoundsBase_ι_InvestParams_ι_withdrawalPeriod : Accessor RoundsBase_ι_InvestParams_ι_withdrawalPeriod :=  {  acc := ·3  }   . 
Global Instance Acc_RoundsBase_ι_InvestParams_ι_withdrawalValue : Accessor RoundsBase_ι_InvestParams_ι_withdrawalValue :=  {  acc := ·4  }   . 
Global Instance Acc_RoundsBase_ι_InvestParams_ι_owner : Accessor RoundsBase_ι_InvestParams_ι_owner :=  {  acc := ·5  }   . 
Global Instance Struct_RoundsBase_ι_StakeValue : Struct RoundsBase_ι_StakeValue :=  {  
 	 fields :=  [  
 		@existT _ _ _ RoundsBase_ι_StakeValue_ι_ordinary 
 
 
 	  ]   ;  
 	 ctor := @RoundsBase_ι_StakeValueC XInteger64 
 }   . 
Global Instance Acc_RoundsBase_ι_StakeValue_ι_ordinary : Accessor RoundsBase_ι_StakeValue_ι_ordinary :=  {  acc := ·0  }   . 
Global Instance Struct_RoundsBase_ι_Round : Struct RoundsBase_ι_Round :=  {  
 	 fields :=  [  
 		@existT _ _ _ RoundsBase_ι_Round_ι_id , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_supposedElectedAt , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_unfreeze , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_step , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_completionReason , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_participantQty , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_stake , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_stakes , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_rewards , 
 
 		@existT _ _ _ RoundsBase_ι_Round_ι_elector , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_vsetHashInElectionPhase , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_proxy , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_start , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_end , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_unused 
 	  ]   ;  
 	 ctor := @RoundsBase_ι_RoundC XInteger64 XInteger32 XHMap XAddress XInteger256 
 }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_id : Accessor RoundsBase_ι_Round_ι_id :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_supposedElectedAt : Accessor RoundsBase_ι_Round_ι_supposedElectedAt :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_unfreeze : Accessor RoundsBase_ι_Round_ι_unfreeze :=  {  acc := ·2  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_step : Accessor RoundsBase_ι_Round_ι_step :=  {  acc := ·3  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_completionReason : Accessor RoundsBase_ι_Round_ι_completionReason :=  {  acc := ·4  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_participantQty : Accessor RoundsBase_ι_Round_ι_participantQty :=  {  acc := ·5  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_stake : Accessor RoundsBase_ι_Round_ι_stake :=  {  acc := ·6  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_stakes : Accessor RoundsBase_ι_Round_ι_stakes :=  {  acc := ·7  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_rewards : Accessor RoundsBase_ι_Round_ι_rewards :=  {  acc := ·8  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_elector : Accessor RoundsBase_ι_Round_ι_elector :=  {  acc := ·9  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_vsetHashInElectionPhase : Accessor RoundsBase_ι_Round_ι_vsetHashInElectionPhase :=  {  acc := ·10  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_proxy : Accessor RoundsBase_ι_Round_ι_proxy :=  {  acc := ·11  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_start : Accessor RoundsBase_ι_Round_ι_start :=  {  acc := ·12  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_end : Accessor RoundsBase_ι_Round_ι_end :=  {  acc := ·13  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_unused : Accessor RoundsBase_ι_Round_ι_unused :=  {  acc := ·14  }   . 
Global Instance Struct_RoundsBase_ι_TruncatedRound : Struct RoundsBase_ι_TruncatedRound :=  {  
 	 fields :=  [  
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_id , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_supposedElectedAt , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_unfreeze , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_step , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_completionReason , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_participantQty , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_stake , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_rewards , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_unused , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_start , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_end , 
 		@existT _ _ _ RoundsBase_ι_TruncatedRound_ι_vsetHash 
 	  ]   ;  
 	 ctor := @RoundsBase_ι_TruncatedRoundC XInteger64 XInteger32 XInteger256 
 }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_id : Accessor RoundsBase_ι_TruncatedRound_ι_id :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_supposedElectedAt : Accessor RoundsBase_ι_TruncatedRound_ι_supposedElectedAt :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_unfreeze : Accessor RoundsBase_ι_TruncatedRound_ι_unfreeze :=  {  acc := ·2  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_step : Accessor RoundsBase_ι_TruncatedRound_ι_step :=  {  acc := ·3  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_completionReason : Accessor RoundsBase_ι_TruncatedRound_ι_completionReason :=  {  acc := ·4  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_participantQty : Accessor RoundsBase_ι_TruncatedRound_ι_participantQty :=  {  acc := ·5  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_stake : Accessor RoundsBase_ι_TruncatedRound_ι_stake :=  {  acc := ·6  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_rewards : Accessor RoundsBase_ι_TruncatedRound_ι_rewards :=  {  acc := ·7  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_unused : Accessor RoundsBase_ι_TruncatedRound_ι_unused :=  {  acc := ·8  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_start : Accessor RoundsBase_ι_TruncatedRound_ι_start :=  {  acc := ·9  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_end : Accessor RoundsBase_ι_TruncatedRound_ι_end :=  {  acc := ·10  }   . 
Global Instance Acc_RoundsBase_ι_TruncatedRound_ι_vsetHash : Accessor RoundsBase_ι_TruncatedRound_ι_vsetHash :=  {  acc := ·11  }   . 
Instance RoundsBase_ι_InvestParams_default : XDefault RoundsBase_ι_InvestParams :=  {  
 	 default := RoundsBase_ι_InvestParamsC default default default default default default  
  }   . 
Instance RoundsBase_ι_StakeValue_default : XDefault RoundsBase_ι_StakeValue :=  {  
 	 default := RoundsBase_ι_StakeValueC default  
  }   . 
Instance RoundsBase_ι_Round_default : XDefault RoundsBase_ι_Round :=  {  
 	 default := RoundsBase_ι_RoundC default default default default default default default default default default default default default default default  
  }   . 
Instance RoundsBase_ι_TruncatedRound_default : XDefault RoundsBase_ι_TruncatedRound :=  {  
 	 default := RoundsBase_ι_TruncatedRoundC default default default default default default default default default default default default  
  }   . 
(* Definition RoundsBaseT := StateT RoundsBase . *) 
 
  
 Definition DePoolContract := @DePoolContractP XInteger8 XInteger64 XInteger16 XBool . 
Global Instance Struct_DePoolContract : Struct DePoolContract :=  { 
 	fields :=  [ 
 		@existT _ _ _ DePoolContract_ι_PART_FRACTION , 
 		@existT _ _ _ DePoolContract_ι_VALIDATOR_FRACTION , 
 		@existT _ _ _ DePoolContract_ι_VALIDATOR_WALLET_MIN_STAKE , 
 		@existT _ _ _ DePoolContract_ι_ADD_STAKE_FEE , 
 		@existT _ _ _ DePoolContract_ι_ADD_VESTING_OR_LOCK_FEE , 
 		@existT _ _ _ DePoolContract_ι_REMOVE_ORDINARY_STAKE_FEE , 
 		@existT _ _ _ DePoolContract_ι_WITHDRAW_PART_AFTER_COMPLETING_FEE , 
 		@existT _ _ _ DePoolContract_ι_WITHDRAW_ALL_AFTER_COMPLETING_FEE , 
 		@existT _ _ _ DePoolContract_ι_TRANSFER_STAKE_FEE , 
 		@existT _ _ _ DePoolContract_ι_RET_OR_REINV_FEE , 
 		@existT _ _ _ DePoolContract_ι_ANSWER_MSG_FEE , 
 		@existT _ _ _ DePoolContract_ι_MAX_MSGS_PER_TR , 
 		@existT _ _ _ DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS , 
 
 		@existT _ _ _ DePoolContract_ι_VALUE_FOR_SELF_CALL , 
 		@existT _ _ _ DePoolContract_ι_STATUS_SUCCESS , 
 		@existT _ _ _ DePoolContract_ι_STATUS_STAKE_TOO_SMALL , 
 		@existT _ _ _ DePoolContract_ι_STATUS_DEPOOL_CLOSED , 
 		@existT _ _ _ DePoolContract_ι_STATUS_ROUND_STAKE_LIMIT , 
 		@existT _ _ _ DePoolContract_ι_STATUS_MSG_VAL_TOO_SMALL , 
 		@existT _ _ _ DePoolContract_ι_STATUS_NO_PARTICIPANT , 
 		@existT _ _ _ DePoolContract_ι_STATUS_NO_TRANSFER_WHILE_PENDING_ROUND , 
 		@existT _ _ _ DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_VESTING , 
 		@existT _ _ _ DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD , 
 		@existT _ _ _ DePoolContract_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS , 
 		@existT _ _ _ DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO , 
 		@existT _ _ _ DePoolContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD , 
 		@existT _ _ _ DePoolContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO , 
 		@existT _ _ _ DePoolContract_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL , 
 		@existT _ _ _ DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_LOCK , 
 		@existT _ _ _ DePoolContract_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG , 
 		@existT _ _ _ DePoolContract_ι_STATUS_TRANSFER_SELF , 
 		@existT _ _ _ DePoolContract_ι_m_poolClosed , 
 		@existT _ _ _ DePoolContract_ι_m_minStake , 
 		@existT _ _ _ DePoolContract_ι_m_minRoundStake , 
 		@existT _ _ _ DePoolContract_ι_m_lastRoundInterest 
 
 
 
 
 
 
 	 ]   ;  
 	 ctor := @DePoolContractC XInteger8 XInteger64 XInteger16 XBool 
 }   . 
Global Instance Acc_DePoolContract_ι_PART_FRACTION : Accessor DePoolContract_ι_PART_FRACTION :=  {  acc := ·0  }   . 
Global Instance Acc_DePoolContract_ι_VALIDATOR_FRACTION : Accessor DePoolContract_ι_VALIDATOR_FRACTION :=  {  acc := ·1  }   . 
Global Instance Acc_DePoolContract_ι_VALIDATOR_WALLET_MIN_STAKE : Accessor DePoolContract_ι_VALIDATOR_WALLET_MIN_STAKE :=  {  acc := ·2  }   . 
Global Instance Acc_DePoolContract_ι_ADD_STAKE_FEE : Accessor DePoolContract_ι_ADD_STAKE_FEE :=  {  acc := ·3  }   . 
Global Instance Acc_DePoolContract_ι_ADD_VESTING_OR_LOCK_FEE : Accessor DePoolContract_ι_ADD_VESTING_OR_LOCK_FEE :=  {  acc := ·4  }   . 
Global Instance Acc_DePoolContract_ι_REMOVE_ORDINARY_STAKE_FEE : Accessor DePoolContract_ι_REMOVE_ORDINARY_STAKE_FEE :=  {  acc := ·5  }   . 
Global Instance Acc_DePoolContract_ι_WITHDRAW_PART_AFTER_COMPLETING_FEE : Accessor DePoolContract_ι_WITHDRAW_PART_AFTER_COMPLETING_FEE :=  {  acc := ·6  }   . 
Global Instance Acc_DePoolContract_ι_WITHDRAW_ALL_AFTER_COMPLETING_FEE : Accessor DePoolContract_ι_WITHDRAW_ALL_AFTER_COMPLETING_FEE :=  {  acc := ·7  }   . 
Global Instance Acc_DePoolContract_ι_TRANSFER_STAKE_FEE : Accessor DePoolContract_ι_TRANSFER_STAKE_FEE :=  {  acc := ·8  }   . 
Global Instance Acc_DePoolContract_ι_RET_OR_REINV_FEE : Accessor DePoolContract_ι_RET_OR_REINV_FEE :=  {  acc := ·9  }   . 
Global Instance Acc_DePoolContract_ι_ANSWER_MSG_FEE : Accessor DePoolContract_ι_ANSWER_MSG_FEE :=  {  acc := ·10  }   . 
Global Instance Acc_DePoolContract_ι_MAX_MSGS_PER_TR : Accessor DePoolContract_ι_MAX_MSGS_PER_TR :=  {  acc := ·11  }   . 
Global Instance Acc_DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS : Accessor DePoolContract_ι_MAX_QTY_OF_OUT_ACTIONS :=  {  acc := ·12  }   . 
Global Instance Acc_DePoolContract_ι_VALUE_FOR_SELF_CALL : Accessor DePoolContract_ι_VALUE_FOR_SELF_CALL :=  {  acc := ·13  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_SUCCESS : Accessor DePoolContract_ι_STATUS_SUCCESS :=  {  acc := ·14  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_STAKE_TOO_SMALL : Accessor DePoolContract_ι_STATUS_STAKE_TOO_SMALL :=  {  acc := ·15  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_DEPOOL_CLOSED : Accessor DePoolContract_ι_STATUS_DEPOOL_CLOSED :=  {  acc := ·16  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_ROUND_STAKE_LIMIT : Accessor DePoolContract_ι_STATUS_ROUND_STAKE_LIMIT :=  {  acc := ·17  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_MSG_VAL_TOO_SMALL : Accessor DePoolContract_ι_STATUS_MSG_VAL_TOO_SMALL :=  {  acc := ·18  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_NO_PARTICIPANT : Accessor DePoolContract_ι_STATUS_NO_PARTICIPANT :=  {  acc := ·19  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_NO_TRANSFER_WHILE_PENDING_ROUND : Accessor DePoolContract_ι_STATUS_NO_TRANSFER_WHILE_PENDING_ROUND :=  {  acc := ·20  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_VESTING : Accessor DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_VESTING :=  {  acc := ·21  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD : Accessor DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD :=  {  acc := ·22  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS : Accessor DePoolContract_ι_STATUS_TOTAL_PERIOD_MORE_18YEARS :=  {  acc := ·23  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO : Accessor DePoolContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO :=  {  acc := ·24  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD : Accessor DePoolContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD :=  {  acc := ·25  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO : Accessor DePoolContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO :=  {  acc := ·26  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL : Accessor DePoolContract_ι_STATUS_REMAINING_STAKE_LESS_THAN_MINIMAL :=  {  acc := ·27  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_LOCK : Accessor DePoolContract_ι_STATUS_PARTICIPANT_HAVE_ALREADY_LOCK :=  {  acc := ·28  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG : Accessor DePoolContract_ι_STATUS_TRANSFER_AMOUNT_IS_TOO_BIG :=  {  acc := ·29  }   . 
Global Instance Acc_DePoolContract_ι_STATUS_TRANSFER_SELF : Accessor DePoolContract_ι_STATUS_TRANSFER_SELF :=  {  acc := ·30  }   . 
Global Instance Acc_DePoolContract_ι_m_poolClosed : Accessor DePoolContract_ι_m_poolClosed :=  {  acc := ·31  }   . 
Global Instance Acc_DePoolContract_ι_m_minStake : Accessor DePoolContract_ι_m_minStake :=  {  acc := ·32  }   . 
Global Instance Acc_DePoolContract_ι_m_minRoundStake : Accessor DePoolContract_ι_m_minRoundStake :=  {  acc := ·33  }   . 
Global Instance Acc_DePoolContract_ι_m_lastRoundInterest : Accessor DePoolContract_ι_m_lastRoundInterest :=  {  acc := ·34  }   . 
Instance DePoolContract_default : XDefault DePoolContract :=  {  
 	 default := DePoolContractC default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default  
  }   . 
(* Definition DePoolContractT := StateT DePoolContract . *) 
    
  
 Definition TestElector_ι_Validator := @TestElector_ι_ValidatorP XInteger64 XInteger256 XInteger32 XInteger8 . 
 Definition TestElector := @TestElectorP XHMap XInteger32 XInteger256 XInteger64 XInteger8 . 
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
 	 ctor := @TestElector_ι_ValidatorC XInteger64 XInteger256 XInteger32 XInteger8 
 }   . 
Global Instance Acc_TestElector_ι_Validator_ι_stake : Accessor TestElector_ι_Validator_ι_stake :=  {  acc := ·0  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_key : Accessor TestElector_ι_Validator_ι_key :=  {  acc := ·1  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_reward : Accessor TestElector_ι_Validator_ι_reward :=  {  acc := ·2  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_qid : Accessor TestElector_ι_Validator_ι_qid :=  {  acc := ·3  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_factor : Accessor TestElector_ι_Validator_ι_factor :=  {  acc := ·4  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_adnl : Accessor TestElector_ι_Validator_ι_adnl :=  {  acc := ·5  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_signature : Accessor TestElector_ι_Validator_ι_signature :=  {  acc := ·6  }   . 
Global Instance Struct_TestElector : Struct TestElector :=  { 
 	fields :=  [ 
 		@existT _ _ _ TestElector_ι_elections , 
 		@existT _ _ _ TestElector_ι_electAt , 
 		@existT _ _ _ TestElector_ι_ELECTIONS_BEGIN_BEFORE , 
 		@existT _ _ _ TestElector_ι_ELECTIONS_END_BEFORE , 
 		@existT _ _ _ TestElector_ι_ELECTED_FOR , 
 		@existT _ _ _ TestElector_ι_STAKE_HELD_FOR 
 
 	 ]   ;  
 	 ctor := @TestElectorC XHMap XInteger32 XInteger256 XInteger64 XInteger8 
 }   . 
Global Instance Acc_TestElector_ι_elections : Accessor TestElector_ι_elections :=  {  acc := ·0  }   . 
Global Instance Acc_TestElector_ι_electAt : Accessor TestElector_ι_electAt :=  {  acc := ·1  }   . 
Global Instance Acc_TestElector_ι_ELECTIONS_BEGIN_BEFORE : Accessor TestElector_ι_ELECTIONS_BEGIN_BEFORE :=  {  acc := ·2  }   . 
Global Instance Acc_TestElector_ι_ELECTIONS_END_BEFORE : Accessor TestElector_ι_ELECTIONS_END_BEFORE :=  {  acc := ·3  }   . 
Global Instance Acc_TestElector_ι_ELECTED_FOR : Accessor TestElector_ι_ELECTED_FOR :=  {  acc := ·4  }   . 
Global Instance Acc_TestElector_ι_STAKE_HELD_FOR : Accessor TestElector_ι_STAKE_HELD_FOR :=  {  acc := ·5  }   . 
Instance TestElector_ι_Validator_default : XDefault TestElector_ι_Validator :=  {  
 	 default := TestElector_ι_ValidatorC default default default default default default default  
  }   . 
Instance TestElector_default : XDefault TestElector :=  {  
 	 default := TestElectorC default default default default default default  
  }   . 
(* Definition TestElectorT := StateT TestElector . *) 
 
  
 Definition VMState := @VMStateP XInteger256 XInteger64 XString XInteger128 TvmCell XList XInteger8 XInteger16 XBool . 
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
 		@existT _ _ _ VMState_ι_savedDePoolContract 
 	 ]   ;  
 	 ctor := @VMStateC XInteger256 XInteger64 XString XInteger128 TvmCell XList XInteger8 XInteger16 XBool 
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
Global Instance Acc_VMState_ι_savedDePoolContract : Accessor VMState_ι_savedDePoolContract :=  {  acc := ·9  }   . 
Instance VMState_default : XDefault VMState :=  {  
 	 default := VMStateC default default default default default default default default default default  
  }   . 
(* Definition VMStateT := StateT VMState . *) 
 
  
 Definition LocalState := @LocalStateP XInteger XInteger64 XAddress TvmCell XBool XInteger256 XInteger32 XInteger8 XInteger128 XInteger16 XHMap . 
Global Instance Struct_LocalState : Struct LocalState :=  { 
 	fields :=  [ 
 		@existT _ _ _ LocalState_ι_getCurValidatorData_Л_t , 
 		@existT _ _ _ LocalState_ι_getPrevValidatorHash_Л_t , 
 		@existT _ _ _ LocalState_ι_getProxy_Л_roundId , 
 		@existT _ _ _ LocalState_ι__recoverStake_Л_proxy , 
 		@existT _ _ _ LocalState_ι__recoverStake_Л_requestId , 
 		@existT _ _ _ LocalState_ι__recoverStake_Л_elector , 
 		@existT _ _ _ LocalState_ι__sendElectionRequest_Л_proxy , 
 		@existT _ _ _ LocalState_ι__sendElectionRequest_Л_requestId , 
 		@existT _ _ _ LocalState_ι__sendElectionRequest_Л_validatorStake , 
 		@existT _ _ _ LocalState_ι__sendElectionRequest_Л_elector , 
 		@existT _ _ _ LocalState_ι_getCurValidatorData_Л_cell , 
 		@existT _ _ _ LocalState_ι_getPrevValidatorHash_Л_cell , 
 		@existT _ _ _ LocalState_ι_roundTimeParams_Л_ok , 
 		@existT _ _ _ LocalState_ι_getMaxStakeFactor_Л_cell , 
 		@existT _ _ _ LocalState_ι_getElector_Л_cell , 
 		@existT _ _ _ LocalState_ι_getOrCreateParticipant_Л_addr , 
 		@existT _ _ _ LocalState_ι__setOrDeleteParticipant_Л_addr , 
 		@existT _ _ _ LocalState_ι_setTimer_Л_timer , 
 		@existT _ _ _ LocalState_ι_updateDePoolPoolAddress_Л_addr , 
 		@existT _ _ _ LocalState_ι_initTimer_Л_timer , 
 		@existT _ _ _ LocalState_ι_initTimer_Л_period , 
 		@existT _ _ _ LocalState_ι__settimer_Л_timer , 
 		@existT _ _ _ LocalState_ι__settimer_Л_period , 
 		@existT _ _ _ LocalState_ι_onTimer_Л_timer , 
 		@existT _ _ _ LocalState_ι_upgrade_Л_newcode , 
 		@existT _ _ _ LocalState_ι_process_new_stake_Л_queryId , 
 		@existT _ _ _ LocalState_ι_process_new_stake_Л_validatorKey , 
 		@existT _ _ _ LocalState_ι_process_new_stake_Л_stakeAt , 
 		@existT _ _ _ LocalState_ι_process_new_stake_Л_maxFactor , 
 		@existT _ _ _ LocalState_ι_process_new_stake_Л_adnlAddr , 
 		@existT _ _ _ LocalState_ι_process_new_stake_Л_signature , 
 		@existT _ _ _ LocalState_ι_process_new_stake_Л_elector , 
 		@existT _ _ _ LocalState_ι_onStakeAccept_Л_queryId , 
 		@existT _ _ _ LocalState_ι_onStakeAccept_Л_comment , 
 		@existT _ _ _ LocalState_ι_onStakeReject_Л_queryId , 
 		@existT _ _ _ LocalState_ι_onStakeReject_Л_comment , 
 		@existT _ _ _ LocalState_ι_recover_stake_Л_queryId , 
 		@existT _ _ _ LocalState_ι_recover_stake_Л_elector , 
 		@existT _ _ _ LocalState_ι_onSuccessToRecoverStake_Л_queryId , 
 		@existT _ _ _ LocalState_ι__addStakes_Л_round , 
 		@existT _ _ _ LocalState_ι__addStakes_Л_participantAddress , 
 		@existT _ _ _ LocalState_ι__addStakes_Л_stake , 
 		@existT _ _ _ LocalState_ι__addStakes_Л_vesting , 
 		@existT _ _ _ LocalState_ι__addStakes_Л_lock , 
 		@existT _ _ _ LocalState_ι_transferStakeInOneRound_Л_round , 
 		@existT _ _ _ LocalState_ι_transferStakeInOneRound_Л_source , 
 		@existT _ _ _ LocalState_ι_transferStakeInOneRound_Л_destination , 
 		@existT _ _ _ LocalState_ι_transferStakeInOneRound_Л_amount , 
 		@existT _ _ _ LocalState_ι_transferStakeInOneRound_Л_minStake , 
 		@existT _ _ _ LocalState_ι_withdrawStakeInPoolingRound_Л_participantAddress , 
 		@existT _ _ _ LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount , 
 		@existT _ _ _ LocalState_ι_withdrawStakeInPoolingRound_Л_minStake , 
 		@existT _ _ _ LocalState_ι_withdrawStakeInPoolingRound_Л_round , 
 		@existT _ _ _ LocalState_ι_sumOfStakes_Л_stakes , 
 		@existT _ _ _ LocalState_ι_toTruncatedRound_Л_round , 
 		@existT _ _ _ LocalState_ι__calcLastRoundInterest_Л_totalStake , 
 		@existT _ _ _ LocalState_ι__calcLastRoundInterest_Л_rewards , 
 		@existT _ _ _ LocalState_ι__sendError_Л_errcode , 
 		@existT _ _ _ LocalState_ι__sendError_Л_comment , 
 		@existT _ _ _ LocalState_ι__sendAccept_Л_fee , 
 		@existT _ _ _ LocalState_ι_startRoundCompleting_Л_round , 
 		@existT _ _ _ LocalState_ι_startRoundCompleting_Л_reason , 
 		@existT _ _ _ LocalState_ι_cutWithdrawalValue_Л_p , 
 		@existT _ _ _ LocalState_ι_cutWithdrawalValue_Л_periodQty , 
 		@existT _ _ _ LocalState_ι__returnOrReinvestForParticipant_Л_completedRound , 
 		@existT _ _ _ LocalState_ι__returnOrReinvestForParticipant_Л_round0 , 
 		@existT _ _ _ LocalState_ι__returnOrReinvestForParticipant_Л_addr , 
 		@existT _ _ _ LocalState_ι__returnOrReinvestForParticipant_Л_stakes , 
 		@existT _ _ _ LocalState_ι__returnOrReinvestForParticipant_Л_validatorIsPunished , 
 		@existT _ _ _ LocalState_ι__returnOrReinvest_Л_round , 
 		@existT _ _ _ LocalState_ι__returnOrReinvest_Л_chunkSize , 
 		@existT _ _ _ LocalState_ι_calculateStakeWithAssert_Л_doSplit , 
 		@existT _ _ _ LocalState_ι_calculateStakeWithAssert_Л_wholeFee , 
 		@existT _ _ _ LocalState_ι_calculateStakeWithAssert_Л_div , 
 		@existT _ _ _ LocalState_ι_addOrdinaryStake_Л_reinvest , 
 		@existT _ _ _ LocalState_ι_removeOrdinaryStake_Л_withdrawValue , 
 		@existT _ _ _ LocalState_ι_addVestingStake_Л_beneficiary , 
 		@existT _ _ _ LocalState_ι_addVestingStake_Л_withdrawalPeriod , 
 		@existT _ _ _ LocalState_ι_addVestingStake_Л_totalPeriod , 
 		@existT _ _ _ LocalState_ι_addLockStake_Л_beneficiary , 
 		@existT _ _ _ LocalState_ι_addLockStake_Л_withdrawalPeriod , 
 		@existT _ _ _ LocalState_ι_addLockStake_Л_totalPeriod , 
 		@existT _ _ _ LocalState_ι_addVestingOrLock_Л_beneficiary , 
 		@existT _ _ _ LocalState_ι_addVestingOrLock_Л_withdrawalPeriod , 
 		@existT _ _ _ LocalState_ι_addVestingOrLock_Л_totalPeriod , 
 		@existT _ _ _ LocalState_ι_addVestingOrLock_Л_isVesting , 
 		@existT _ _ _ LocalState_ι_withdrawPartAfterCompleting_Л_withdrawValue , 
 		@existT _ _ _ LocalState_ι_withdrawAllAfterCompleting_Л_doWithdrawAll , 
 		@existT _ _ _ LocalState_ι_transferStake_Л_dest , 
 		@existT _ _ _ LocalState_ι_transferStake_Л_amount , 
 		@existT _ _ _ LocalState_ι_participateInElections_Л_queryId , 
 		@existT _ _ _ LocalState_ι_participateInElections_Л_validatorKey , 
 		@existT _ _ _ LocalState_ι_participateInElections_Л_stakeAt , 
 		@existT _ _ _ LocalState_ι_participateInElections_Л_maxFactor , 
 		@existT _ _ _ LocalState_ι_participateInElections_Л_adnlAddr , 
 		@existT _ _ _ LocalState_ι_participateInElections_Л_signature , 
 		@existT _ _ _ LocalState_ι_participateInElections_Л_WaitingValidatorRequest , 
 		@existT _ _ _ LocalState_ι_generateRound_Л_MAX_TIME , 
 		@existT _ _ _ LocalState_ι_generateRound_Л_Pooling , 
 		@existT _ _ _ LocalState_ι_generateRound_Л_Undefined , 
 		@existT _ _ _ LocalState_ι_updateRound2_Л_round2 , 
 		@existT _ _ _ LocalState_ι_updateRound2_Л_prevValidatorHash , 
 		@existT _ _ _ LocalState_ι_updateRound2_Л_curValidatorHash , 
 		@existT _ _ _ LocalState_ι_updateRound2_Л_validationStart , 
 		@existT _ _ _ LocalState_ι_updateRound2_Л_stakeHeldFor , 
 		@existT _ _ _ LocalState_ι_updateRounds_Л_validationStart , 
 		@existT _ _ _ LocalState_ι_completeRoundWithChunk_Л_roundId , 
 		@existT _ _ _ LocalState_ι_completeRoundWithChunk_Л_chunkSize , 
 		@existT _ _ _ LocalState_ι_completeRoundWithChunk_Л_Completing , 
 		@existT _ _ _ LocalState_ι_completeRound_Л_roundId , 
 		@existT _ _ _ LocalState_ι_completeRound_Л_participantQty , 
 		@existT _ _ _ LocalState_ι_completeRound_Л_Completing , 
 		@existT _ _ _ LocalState_ι_onStakeAccept_Л_elector , 
 		@existT _ _ _ LocalState_ι_onStakeAccept_Л_WaitingIfStakeAccepted , 
 		@existT _ _ _ LocalState_ι_onStakeReject_Л_elector , 
 		@existT _ _ _ LocalState_ι_onStakeReject_Л_WaitingIfStakeAccepted , 
 		@existT _ _ _ LocalState_ι_acceptRewardAndStartRoundCompleting_Л_round , 
 		@existT _ _ _ LocalState_ι_acceptRewardAndStartRoundCompleting_Л_value , 
 		@existT _ _ _ LocalState_ι_acceptRewardAndStartRoundCompleting_Л_effectiveStake , 
 		@existT _ _ _ LocalState_ι_onSuccessToRecoverStake_Л_elector , 
 		@existT _ _ _ LocalState_ι_onFailToRecoverStake_Л_queryId , 
 		@existT _ _ _ LocalState_ι_onFailToRecoverStake_Л_elector , 
 		@existT _ _ _ LocalState_ι_getParticipantInfo_Л_addr , 
 		@existT _ _ _ LocalState_ι_onRoundComplete_Л_roundId , 
 		@existT _ _ _ LocalState_ι_onRoundComplete_Л_reward , 
 		@existT _ _ _ LocalState_ι_onRoundComplete_Л_ordinaryStake , 
 		@existT _ _ _ LocalState_ι_onRoundComplete_Л_vestingStake , 
 		@existT _ _ _ LocalState_ι_onRoundComplete_Л_lockStake , 
 		@existT _ _ _ LocalState_ι_onRoundComplete_Л_reinvest , 
 		@existT _ _ _ LocalState_ι_onRoundComplete_Л_reason , 
 		@existT _ _ _ LocalState_ι_receiveAnswer_Л_errcode , 
 		@existT _ _ _ LocalState_ι_receiveAnswer_Л_comment , 
 		@existT _ _ _ LocalState_ι_onTransfer_Л_source , 
 		@existT _ _ _ LocalState_ι_onTransfer_Л_amount , 
 		@existT _ _ _ LocalState_ι_sendTransaction_Л_dest , 
 		@existT _ _ _ LocalState_ι_sendTransaction_Л_value , 
 		@existT _ _ _ LocalState_ι_sendTransaction_Л_bounce , 
 		@existT _ _ _ LocalState_ι_sendTransaction_Л_flags , 
 		@existT _ _ _ LocalState_ι_sendTransaction_Л_payload , 
 		@existT _ _ _ LocalState_ι_acceptRecoveredStake_Л_queryId , 
 		@existT _ _ _ LocalState_ι_sendError_Л_queryId , 
 		@existT _ _ _ LocalState_ι_sendError_Л_op 
 	 ]   ;  
 	 ctor := @LocalStateC XInteger XInteger64 XAddress TvmCell XBool XInteger256 XInteger32 XInteger8 XInteger128 XInteger16 XHMap 
 }   . 
Global Instance Acc_LocalState_ι_getCurValidatorData_Л_t : Accessor LocalState_ι_getCurValidatorData_Л_t :=  {  acc := ·0  }   . 
Global Instance Acc_LocalState_ι_getPrevValidatorHash_Л_t : Accessor LocalState_ι_getPrevValidatorHash_Л_t :=  {  acc := ·1  }   . 
Global Instance Acc_LocalState_ι_getProxy_Л_roundId : Accessor LocalState_ι_getProxy_Л_roundId :=  {  acc := ·2  }   . 
Global Instance Acc_LocalState_ι__recoverStake_Л_proxy : Accessor LocalState_ι__recoverStake_Л_proxy :=  {  acc := ·3  }   . 
Global Instance Acc_LocalState_ι__recoverStake_Л_requestId : Accessor LocalState_ι__recoverStake_Л_requestId :=  {  acc := ·4  }   . 
Global Instance Acc_LocalState_ι__recoverStake_Л_elector : Accessor LocalState_ι__recoverStake_Л_elector :=  {  acc := ·5  }   . 
Global Instance Acc_LocalState_ι__sendElectionRequest_Л_proxy : Accessor LocalState_ι__sendElectionRequest_Л_proxy :=  {  acc := ·6  }   . 
Global Instance Acc_LocalState_ι__sendElectionRequest_Л_requestId : Accessor LocalState_ι__sendElectionRequest_Л_requestId :=  {  acc := ·7  }   . 
Global Instance Acc_LocalState_ι__sendElectionRequest_Л_validatorStake : Accessor LocalState_ι__sendElectionRequest_Л_validatorStake :=  {  acc := ·8  }   . 
Global Instance Acc_LocalState_ι__sendElectionRequest_Л_elector : Accessor LocalState_ι__sendElectionRequest_Л_elector :=  {  acc := ·9  }   . 
Global Instance Acc_LocalState_ι_getCurValidatorData_Л_cell : Accessor LocalState_ι_getCurValidatorData_Л_cell :=  {  acc := ·10  }   . 
Global Instance Acc_LocalState_ι_getPrevValidatorHash_Л_cell : Accessor LocalState_ι_getPrevValidatorHash_Л_cell :=  {  acc := ·11  }   . 
Global Instance Acc_LocalState_ι_roundTimeParams_Л_ok : Accessor LocalState_ι_roundTimeParams_Л_ok :=  {  acc := ·12  }   . 
Global Instance Acc_LocalState_ι_getMaxStakeFactor_Л_cell : Accessor LocalState_ι_getMaxStakeFactor_Л_cell :=  {  acc := ·13  }   . 
Global Instance Acc_LocalState_ι_getElector_Л_cell : Accessor LocalState_ι_getElector_Л_cell :=  {  acc := ·14  }   . 
Global Instance Acc_LocalState_ι_getOrCreateParticipant_Л_addr : Accessor LocalState_ι_getOrCreateParticipant_Л_addr :=  {  acc := ·15  }   . 
Global Instance Acc_LocalState_ι__setOrDeleteParticipant_Л_addr : Accessor LocalState_ι__setOrDeleteParticipant_Л_addr :=  {  acc := ·16  }   . 
Global Instance Acc_LocalState_ι_setTimer_Л_timer : Accessor LocalState_ι_setTimer_Л_timer :=  {  acc := ·17  }   . 
Global Instance Acc_LocalState_ι_updateDePoolPoolAddress_Л_addr : Accessor LocalState_ι_updateDePoolPoolAddress_Л_addr :=  {  acc := ·18  }   . 
Global Instance Acc_LocalState_ι_initTimer_Л_timer : Accessor LocalState_ι_initTimer_Л_timer :=  {  acc := ·19  }   . 
Global Instance Acc_LocalState_ι_initTimer_Л_period : Accessor LocalState_ι_initTimer_Л_period :=  {  acc := ·20  }   . 
Global Instance Acc_LocalState_ι__settimer_Л_timer : Accessor LocalState_ι__settimer_Л_timer :=  {  acc := ·21  }   . 
Global Instance Acc_LocalState_ι__settimer_Л_period : Accessor LocalState_ι__settimer_Л_period :=  {  acc := ·22  }   . 
Global Instance Acc_LocalState_ι_onTimer_Л_timer : Accessor LocalState_ι_onTimer_Л_timer :=  {  acc := ·23  }   . 
Global Instance Acc_LocalState_ι_upgrade_Л_newcode : Accessor LocalState_ι_upgrade_Л_newcode :=  {  acc := ·24  }   . 
Global Instance Acc_LocalState_ι_process_new_stake_Л_queryId : Accessor LocalState_ι_process_new_stake_Л_queryId :=  {  acc := ·25  }   . 
Global Instance Acc_LocalState_ι_process_new_stake_Л_validatorKey : Accessor LocalState_ι_process_new_stake_Л_validatorKey :=  {  acc := ·26  }   . 
Global Instance Acc_LocalState_ι_process_new_stake_Л_stakeAt : Accessor LocalState_ι_process_new_stake_Л_stakeAt :=  {  acc := ·27  }   . 
Global Instance Acc_LocalState_ι_process_new_stake_Л_maxFactor : Accessor LocalState_ι_process_new_stake_Л_maxFactor :=  {  acc := ·28  }   . 
Global Instance Acc_LocalState_ι_process_new_stake_Л_adnlAddr : Accessor LocalState_ι_process_new_stake_Л_adnlAddr :=  {  acc := ·29  }   . 
Global Instance Acc_LocalState_ι_process_new_stake_Л_signature : Accessor LocalState_ι_process_new_stake_Л_signature :=  {  acc := ·30  }   . 
Global Instance Acc_LocalState_ι_process_new_stake_Л_elector : Accessor LocalState_ι_process_new_stake_Л_elector :=  {  acc := ·31  }   . 
Global Instance Acc_LocalState_ι_onStakeAccept_Л_queryId : Accessor LocalState_ι_onStakeAccept_Л_queryId :=  {  acc := ·32  }   . 
Global Instance Acc_LocalState_ι_onStakeAccept_Л_comment : Accessor LocalState_ι_onStakeAccept_Л_comment :=  {  acc := ·33  }   . 
Global Instance Acc_LocalState_ι_onStakeReject_Л_queryId : Accessor LocalState_ι_onStakeReject_Л_queryId :=  {  acc := ·34  }   . 
Global Instance Acc_LocalState_ι_onStakeReject_Л_comment : Accessor LocalState_ι_onStakeReject_Л_comment :=  {  acc := ·35  }   . 
Global Instance Acc_LocalState_ι_recover_stake_Л_queryId : Accessor LocalState_ι_recover_stake_Л_queryId :=  {  acc := ·36  }   . 
Global Instance Acc_LocalState_ι_recover_stake_Л_elector : Accessor LocalState_ι_recover_stake_Л_elector :=  {  acc := ·37  }   . 
Global Instance Acc_LocalState_ι_onSuccessToRecoverStake_Л_queryId : Accessor LocalState_ι_onSuccessToRecoverStake_Л_queryId :=  {  acc := ·38  }   . 
Global Instance Acc_LocalState_ι__addStakes_Л_round : Accessor LocalState_ι__addStakes_Л_round :=  {  acc := ·39  }   . 
Global Instance Acc_LocalState_ι__addStakes_Л_participantAddress : Accessor LocalState_ι__addStakes_Л_participantAddress :=  {  acc := ·40  }   . 
Global Instance Acc_LocalState_ι__addStakes_Л_stake : Accessor LocalState_ι__addStakes_Л_stake :=  {  acc := ·41  }   . 
Global Instance Acc_LocalState_ι__addStakes_Л_vesting : Accessor LocalState_ι__addStakes_Л_vesting :=  {  acc := ·42  }   . 
Global Instance Acc_LocalState_ι__addStakes_Л_lock : Accessor LocalState_ι__addStakes_Л_lock :=  {  acc := ·43  }   . 
Global Instance Acc_LocalState_ι_transferStakeInOneRound_Л_round : Accessor LocalState_ι_transferStakeInOneRound_Л_round :=  {  acc := ·44  }   . 
Global Instance Acc_LocalState_ι_transferStakeInOneRound_Л_source : Accessor LocalState_ι_transferStakeInOneRound_Л_source :=  {  acc := ·45  }   . 
Global Instance Acc_LocalState_ι_transferStakeInOneRound_Л_destination : Accessor LocalState_ι_transferStakeInOneRound_Л_destination :=  {  acc := ·46  }   . 
Global Instance Acc_LocalState_ι_transferStakeInOneRound_Л_amount : Accessor LocalState_ι_transferStakeInOneRound_Л_amount :=  {  acc := ·47  }   . 
Global Instance Acc_LocalState_ι_transferStakeInOneRound_Л_minStake : Accessor LocalState_ι_transferStakeInOneRound_Л_minStake :=  {  acc := ·48  }   . 
Global Instance Acc_LocalState_ι_withdrawStakeInPoolingRound_Л_participantAddress : Accessor LocalState_ι_withdrawStakeInPoolingRound_Л_participantAddress :=  {  acc := ·49  }   . 
Global Instance Acc_LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount : Accessor LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount :=  {  acc := ·50  }   . 
Global Instance Acc_LocalState_ι_withdrawStakeInPoolingRound_Л_minStake : Accessor LocalState_ι_withdrawStakeInPoolingRound_Л_minStake :=  {  acc := ·51  }   . 
Global Instance Acc_LocalState_ι_withdrawStakeInPoolingRound_Л_round : Accessor LocalState_ι_withdrawStakeInPoolingRound_Л_round :=  {  acc := ·52  }   . 
Global Instance Acc_LocalState_ι_sumOfStakes_Л_stakes : Accessor LocalState_ι_sumOfStakes_Л_stakes :=  {  acc := ·53  }   . 
Global Instance Acc_LocalState_ι_toTruncatedRound_Л_round : Accessor LocalState_ι_toTruncatedRound_Л_round :=  {  acc := ·54  }   . 
Global Instance Acc_LocalState_ι__calcLastRoundInterest_Л_totalStake : Accessor LocalState_ι__calcLastRoundInterest_Л_totalStake :=  {  acc := ·55  }   . 
Global Instance Acc_LocalState_ι__calcLastRoundInterest_Л_rewards : Accessor LocalState_ι__calcLastRoundInterest_Л_rewards :=  {  acc := ·56  }   . 
Global Instance Acc_LocalState_ι__sendError_Л_errcode : Accessor LocalState_ι__sendError_Л_errcode :=  {  acc := ·57  }   . 
Global Instance Acc_LocalState_ι__sendError_Л_comment : Accessor LocalState_ι__sendError_Л_comment :=  {  acc := ·58  }   . 
Global Instance Acc_LocalState_ι__sendAccept_Л_fee : Accessor LocalState_ι__sendAccept_Л_fee :=  {  acc := ·59  }   . 
Global Instance Acc_LocalState_ι_startRoundCompleting_Л_round : Accessor LocalState_ι_startRoundCompleting_Л_round :=  {  acc := ·60  }   . 
Global Instance Acc_LocalState_ι_startRoundCompleting_Л_reason : Accessor LocalState_ι_startRoundCompleting_Л_reason :=  {  acc := ·61  }   . 
Global Instance Acc_LocalState_ι_cutWithdrawalValue_Л_p : Accessor LocalState_ι_cutWithdrawalValue_Л_p :=  {  acc := ·62  }   . 
Global Instance Acc_LocalState_ι_cutWithdrawalValue_Л_periodQty : Accessor LocalState_ι_cutWithdrawalValue_Л_periodQty :=  {  acc := ·63  }   . 
Global Instance Acc_LocalState_ι__returnOrReinvestForParticipant_Л_completedRound : Accessor LocalState_ι__returnOrReinvestForParticipant_Л_completedRound :=  {  acc := ·64  }   . 
Global Instance Acc_LocalState_ι__returnOrReinvestForParticipant_Л_round0 : Accessor LocalState_ι__returnOrReinvestForParticipant_Л_round0 :=  {  acc := ·65  }   . 
Global Instance Acc_LocalState_ι__returnOrReinvestForParticipant_Л_addr : Accessor LocalState_ι__returnOrReinvestForParticipant_Л_addr :=  {  acc := ·66  }   . 
Global Instance Acc_LocalState_ι__returnOrReinvestForParticipant_Л_stakes : Accessor LocalState_ι__returnOrReinvestForParticipant_Л_stakes :=  {  acc := ·67  }   . 
Global Instance Acc_LocalState_ι__returnOrReinvestForParticipant_Л_validatorIsPunished : Accessor LocalState_ι__returnOrReinvestForParticipant_Л_validatorIsPunished :=  {  acc := ·68  }   . 
Global Instance Acc_LocalState_ι__returnOrReinvest_Л_round : Accessor LocalState_ι__returnOrReinvest_Л_round :=  {  acc := ·69  }   . 
Global Instance Acc_LocalState_ι__returnOrReinvest_Л_chunkSize : Accessor LocalState_ι__returnOrReinvest_Л_chunkSize :=  {  acc := ·70  }   . 
Global Instance Acc_LocalState_ι_calculateStakeWithAssert_Л_doSplit : Accessor LocalState_ι_calculateStakeWithAssert_Л_doSplit :=  {  acc := ·71  }   . 
Global Instance Acc_LocalState_ι_calculateStakeWithAssert_Л_wholeFee : Accessor LocalState_ι_calculateStakeWithAssert_Л_wholeFee :=  {  acc := ·72  }   . 
Global Instance Acc_LocalState_ι_calculateStakeWithAssert_Л_div : Accessor LocalState_ι_calculateStakeWithAssert_Л_div :=  {  acc := ·73  }   . 
Global Instance Acc_LocalState_ι_addOrdinaryStake_Л_reinvest : Accessor LocalState_ι_addOrdinaryStake_Л_reinvest :=  {  acc := ·74  }   . 
Global Instance Acc_LocalState_ι_removeOrdinaryStake_Л_withdrawValue : Accessor LocalState_ι_removeOrdinaryStake_Л_withdrawValue :=  {  acc := ·75  }   . 
Global Instance Acc_LocalState_ι_addVestingStake_Л_beneficiary : Accessor LocalState_ι_addVestingStake_Л_beneficiary :=  {  acc := ·76  }   . 
Global Instance Acc_LocalState_ι_addVestingStake_Л_withdrawalPeriod : Accessor LocalState_ι_addVestingStake_Л_withdrawalPeriod :=  {  acc := ·77  }   . 
Global Instance Acc_LocalState_ι_addVestingStake_Л_totalPeriod : Accessor LocalState_ι_addVestingStake_Л_totalPeriod :=  {  acc := ·78  }   . 
Global Instance Acc_LocalState_ι_addLockStake_Л_beneficiary : Accessor LocalState_ι_addLockStake_Л_beneficiary :=  {  acc := ·79  }   . 
Global Instance Acc_LocalState_ι_addLockStake_Л_withdrawalPeriod : Accessor LocalState_ι_addLockStake_Л_withdrawalPeriod :=  {  acc := ·80  }   . 
Global Instance Acc_LocalState_ι_addLockStake_Л_totalPeriod : Accessor LocalState_ι_addLockStake_Л_totalPeriod :=  {  acc := ·81  }   . 
Global Instance Acc_LocalState_ι_addVestingOrLock_Л_beneficiary : Accessor LocalState_ι_addVestingOrLock_Л_beneficiary :=  {  acc := ·82  }   . 
Global Instance Acc_LocalState_ι_addVestingOrLock_Л_withdrawalPeriod : Accessor LocalState_ι_addVestingOrLock_Л_withdrawalPeriod :=  {  acc := ·83  }   . 
Global Instance Acc_LocalState_ι_addVestingOrLock_Л_totalPeriod : Accessor LocalState_ι_addVestingOrLock_Л_totalPeriod :=  {  acc := ·84  }   . 
Global Instance Acc_LocalState_ι_addVestingOrLock_Л_isVesting : Accessor LocalState_ι_addVestingOrLock_Л_isVesting :=  {  acc := ·85  }   . 
Global Instance Acc_LocalState_ι_withdrawPartAfterCompleting_Л_withdrawValue : Accessor LocalState_ι_withdrawPartAfterCompleting_Л_withdrawValue :=  {  acc := ·86  }   . 
Global Instance Acc_LocalState_ι_withdrawAllAfterCompleting_Л_doWithdrawAll : Accessor LocalState_ι_withdrawAllAfterCompleting_Л_doWithdrawAll :=  {  acc := ·87  }   . 
Global Instance Acc_LocalState_ι_transferStake_Л_dest : Accessor LocalState_ι_transferStake_Л_dest :=  {  acc := ·88  }   . 
Global Instance Acc_LocalState_ι_transferStake_Л_amount : Accessor LocalState_ι_transferStake_Л_amount :=  {  acc := ·89  }   . 
Global Instance Acc_LocalState_ι_participateInElections_Л_queryId : Accessor LocalState_ι_participateInElections_Л_queryId :=  {  acc := ·90  }   . 
Global Instance Acc_LocalState_ι_participateInElections_Л_validatorKey : Accessor LocalState_ι_participateInElections_Л_validatorKey :=  {  acc := ·91  }   . 
Global Instance Acc_LocalState_ι_participateInElections_Л_stakeAt : Accessor LocalState_ι_participateInElections_Л_stakeAt :=  {  acc := ·92  }   . 
Global Instance Acc_LocalState_ι_participateInElections_Л_maxFactor : Accessor LocalState_ι_participateInElections_Л_maxFactor :=  {  acc := ·93  }   . 
Global Instance Acc_LocalState_ι_participateInElections_Л_adnlAddr : Accessor LocalState_ι_participateInElections_Л_adnlAddr :=  {  acc := ·94  }   . 
Global Instance Acc_LocalState_ι_participateInElections_Л_signature : Accessor LocalState_ι_participateInElections_Л_signature :=  {  acc := ·95  }   . 
Global Instance Acc_LocalState_ι_participateInElections_Л_WaitingValidatorRequest : Accessor LocalState_ι_participateInElections_Л_WaitingValidatorRequest :=  {  acc := ·96  }   . 
Global Instance Acc_LocalState_ι_generateRound_Л_MAX_TIME : Accessor LocalState_ι_generateRound_Л_MAX_TIME :=  {  acc := ·97  }   . 
Global Instance Acc_LocalState_ι_generateRound_Л_Pooling : Accessor LocalState_ι_generateRound_Л_Pooling :=  {  acc := ·98  }   . 
Global Instance Acc_LocalState_ι_generateRound_Л_Undefined : Accessor LocalState_ι_generateRound_Л_Undefined :=  {  acc := ·99  }   . 
Global Instance Acc_LocalState_ι_updateRound2_Л_round2 : Accessor LocalState_ι_updateRound2_Л_round2 :=  {  acc := ·100  }   . 
Global Instance Acc_LocalState_ι_updateRound2_Л_prevValidatorHash : Accessor LocalState_ι_updateRound2_Л_prevValidatorHash :=  {  acc := ·101  }   . 
Global Instance Acc_LocalState_ι_updateRound2_Л_curValidatorHash : Accessor LocalState_ι_updateRound2_Л_curValidatorHash :=  {  acc := ·102  }   . 
Global Instance Acc_LocalState_ι_updateRound2_Л_validationStart : Accessor LocalState_ι_updateRound2_Л_validationStart :=  {  acc := ·103  }   . 
Global Instance Acc_LocalState_ι_updateRound2_Л_stakeHeldFor : Accessor LocalState_ι_updateRound2_Л_stakeHeldFor :=  {  acc := ·104  }   . 
Global Instance Acc_LocalState_ι_updateRounds_Л_validationStart : Accessor LocalState_ι_updateRounds_Л_validationStart :=  {  acc := ·105  }   . 
Global Instance Acc_LocalState_ι_completeRoundWithChunk_Л_roundId : Accessor LocalState_ι_completeRoundWithChunk_Л_roundId :=  {  acc := ·106  }   . 
Global Instance Acc_LocalState_ι_completeRoundWithChunk_Л_chunkSize : Accessor LocalState_ι_completeRoundWithChunk_Л_chunkSize :=  {  acc := ·107  }   . 
Global Instance Acc_LocalState_ι_completeRoundWithChunk_Л_Completing : Accessor LocalState_ι_completeRoundWithChunk_Л_Completing :=  {  acc := ·108  }   . 
Global Instance Acc_LocalState_ι_completeRound_Л_roundId : Accessor LocalState_ι_completeRound_Л_roundId :=  {  acc := ·109  }   . 
Global Instance Acc_LocalState_ι_completeRound_Л_participantQty : Accessor LocalState_ι_completeRound_Л_participantQty :=  {  acc := ·110  }   . 
Global Instance Acc_LocalState_ι_completeRound_Л_Completing : Accessor LocalState_ι_completeRound_Л_Completing :=  {  acc := ·111  }   . 
Global Instance Acc_LocalState_ι_onStakeAccept_Л_elector : Accessor LocalState_ι_onStakeAccept_Л_elector :=  {  acc := ·112  }   . 
Global Instance Acc_LocalState_ι_onStakeAccept_Л_WaitingIfStakeAccepted : Accessor LocalState_ι_onStakeAccept_Л_WaitingIfStakeAccepted :=  {  acc := ·113  }   . 
Global Instance Acc_LocalState_ι_onStakeReject_Л_elector : Accessor LocalState_ι_onStakeReject_Л_elector :=  {  acc := ·114  }   . 
Global Instance Acc_LocalState_ι_onStakeReject_Л_WaitingIfStakeAccepted : Accessor LocalState_ι_onStakeReject_Л_WaitingIfStakeAccepted :=  {  acc := ·115  }   . 
Global Instance Acc_LocalState_ι_acceptRewardAndStartRoundCompleting_Л_round : Accessor LocalState_ι_acceptRewardAndStartRoundCompleting_Л_round :=  {  acc := ·116  }   . 
Global Instance Acc_LocalState_ι_acceptRewardAndStartRoundCompleting_Л_value : Accessor LocalState_ι_acceptRewardAndStartRoundCompleting_Л_value :=  {  acc := ·117  }   . 
Global Instance Acc_LocalState_ι_acceptRewardAndStartRoundCompleting_Л_effectiveStake : Accessor LocalState_ι_acceptRewardAndStartRoundCompleting_Л_effectiveStake :=  {  acc := ·118  }   . 
Global Instance Acc_LocalState_ι_onSuccessToRecoverStake_Л_elector : Accessor LocalState_ι_onSuccessToRecoverStake_Л_elector :=  {  acc := ·119  }   . 
Global Instance Acc_LocalState_ι_onFailToRecoverStake_Л_queryId : Accessor LocalState_ι_onFailToRecoverStake_Л_queryId :=  {  acc := ·120  }   . 
Global Instance Acc_LocalState_ι_onFailToRecoverStake_Л_elector : Accessor LocalState_ι_onFailToRecoverStake_Л_elector :=  {  acc := ·121  }   . 
Global Instance Acc_LocalState_ι_getParticipantInfo_Л_addr : Accessor LocalState_ι_getParticipantInfo_Л_addr :=  {  acc := ·122  }   . 
Global Instance Acc_LocalState_ι_onRoundComplete_Л_roundId : Accessor LocalState_ι_onRoundComplete_Л_roundId :=  {  acc := ·123  }   . 
Global Instance Acc_LocalState_ι_onRoundComplete_Л_reward : Accessor LocalState_ι_onRoundComplete_Л_reward :=  {  acc := ·124  }   . 
Global Instance Acc_LocalState_ι_onRoundComplete_Л_ordinaryStake : Accessor LocalState_ι_onRoundComplete_Л_ordinaryStake :=  {  acc := ·125  }   . 
Global Instance Acc_LocalState_ι_onRoundComplete_Л_vestingStake : Accessor LocalState_ι_onRoundComplete_Л_vestingStake :=  {  acc := ·126  }   . 
Global Instance Acc_LocalState_ι_onRoundComplete_Л_lockStake : Accessor LocalState_ι_onRoundComplete_Л_lockStake :=  {  acc := ·127  }   . 
Global Instance Acc_LocalState_ι_onRoundComplete_Л_reinvest : Accessor LocalState_ι_onRoundComplete_Л_reinvest :=  {  acc := ·128  }   . 
Global Instance Acc_LocalState_ι_onRoundComplete_Л_reason : Accessor LocalState_ι_onRoundComplete_Л_reason :=  {  acc := ·129  }   . 
Global Instance Acc_LocalState_ι_receiveAnswer_Л_errcode : Accessor LocalState_ι_receiveAnswer_Л_errcode :=  {  acc := ·130  }   . 
Global Instance Acc_LocalState_ι_receiveAnswer_Л_comment : Accessor LocalState_ι_receiveAnswer_Л_comment :=  {  acc := ·131  }   . 
Global Instance Acc_LocalState_ι_onTransfer_Л_source : Accessor LocalState_ι_onTransfer_Л_source :=  {  acc := ·132  }   . 
Global Instance Acc_LocalState_ι_onTransfer_Л_amount : Accessor LocalState_ι_onTransfer_Л_amount :=  {  acc := ·133  }   . 
Global Instance Acc_LocalState_ι_sendTransaction_Л_dest : Accessor LocalState_ι_sendTransaction_Л_dest :=  {  acc := ·134  }   . 
Global Instance Acc_LocalState_ι_sendTransaction_Л_value : Accessor LocalState_ι_sendTransaction_Л_value :=  {  acc := ·135  }   . 
Global Instance Acc_LocalState_ι_sendTransaction_Л_bounce : Accessor LocalState_ι_sendTransaction_Л_bounce :=  {  acc := ·136  }   . 
Global Instance Acc_LocalState_ι_sendTransaction_Л_flags : Accessor LocalState_ι_sendTransaction_Л_flags :=  {  acc := ·137  }   . 
Global Instance Acc_LocalState_ι_sendTransaction_Л_payload : Accessor LocalState_ι_sendTransaction_Л_payload :=  {  acc := ·138  }   . 
Global Instance Acc_LocalState_ι_acceptRecoveredStake_Л_queryId : Accessor LocalState_ι_acceptRecoveredStake_Л_queryId :=  {  acc := ·139  }   . 
Global Instance Acc_LocalState_ι_sendError_Л_queryId : Accessor LocalState_ι_sendError_Л_queryId :=  {  acc := ·140  }   . 
Global Instance Acc_LocalState_ι_sendError_Л_op : Accessor LocalState_ι_sendError_Л_op :=  {  acc := ·141  }   . 
Instance LocalState_default : XDefault LocalState :=  {  
 	 default := LocalStateC default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default  
  }   . 
(* Definition LocalStateT := StateT LocalState . *) 
 
  
 Definition Ledger := @LedgerP XInteger32 XAddress XHMap XInteger8 XInteger64 XBool XInteger XInteger16 XInteger256 XString XInteger128 TvmCell XList . 
Global Instance Struct_Ledger : Struct Ledger :=  { 
 	fields :=  [ 
 		@existT _ _ _ Ledger_ι_DebugDePool , 
 		@existT _ _ _ Ledger_ι_AcceptBase , 
 		@existT _ _ _ Ledger_ι_ValidatorBase , 
 		@existT _ _ _ Ledger_ι_ProxyBase , 
 		@existT _ _ _ Ledger_ι_ConfigParamsBase , 
 		@existT _ _ _ Ledger_ι_ParticipantBase , 
 		@existT _ _ _ Ledger_ι_DePoolHelper , 
 		@existT _ _ _ Ledger_ι_Errors , 
 		@existT _ _ _ Ledger_ι_InternalErrors , 
 		@existT _ _ _ Ledger_ι_DePoolLib , 
 		@existT _ _ _ Ledger_ι_DePoolProxyContract , 
 		@existT _ _ _ Ledger_ι_RoundsBase , 
 		@existT _ _ _ Ledger_ι_DePoolContract , 
 		@existT _ _ _ Ledger_ι_DePool , 
 		@existT _ _ _ Ledger_ι_Participant , 
 		@existT _ _ _ Ledger_ι_TestElector , 
 		@existT _ _ _ Ledger_ι_VMState , 
 		@existT _ _ _ Ledger_ι_LocalState 
 	 ]   ;  
 	 ctor := @LedgerC XInteger32 XAddress XHMap XInteger8 XInteger64 XBool XInteger XInteger16 XInteger256 XString XInteger128 TvmCell XList 
 }   . 
Global Instance Acc_Ledger_ι_DebugDePool : Accessor Ledger_ι_DebugDePool :=  {  acc := ·0  }   . 
Global Instance Acc_Ledger_ι_AcceptBase : Accessor Ledger_ι_AcceptBase :=  {  acc := ·1  }   . 
Global Instance Acc_Ledger_ι_ValidatorBase : Accessor Ledger_ι_ValidatorBase :=  {  acc := ·2  }   . 
Global Instance Acc_Ledger_ι_ProxyBase : Accessor Ledger_ι_ProxyBase :=  {  acc := ·3  }   . 
Global Instance Acc_Ledger_ι_ConfigParamsBase : Accessor Ledger_ι_ConfigParamsBase :=  {  acc := ·4  }   . 
Global Instance Acc_Ledger_ι_ParticipantBase : Accessor Ledger_ι_ParticipantBase :=  {  acc := ·5  }   . 
Global Instance Acc_Ledger_ι_DePoolHelper : Accessor Ledger_ι_DePoolHelper :=  {  acc := ·6  }   . 
Global Instance Acc_Ledger_ι_Errors : Accessor Ledger_ι_Errors :=  {  acc := ·7  }   . 
Global Instance Acc_Ledger_ι_InternalErrors : Accessor Ledger_ι_InternalErrors :=  {  acc := ·8  }   . 
Global Instance Acc_Ledger_ι_DePoolLib : Accessor Ledger_ι_DePoolLib :=  {  acc := ·9  }   . 
Global Instance Acc_Ledger_ι_DePoolProxyContract : Accessor Ledger_ι_DePoolProxyContract :=  {  acc := ·10  }   . 
Global Instance Acc_Ledger_ι_RoundsBase : Accessor Ledger_ι_RoundsBase :=  {  acc := ·11  }   . 
Global Instance Acc_Ledger_ι_DePoolContract : Accessor Ledger_ι_DePoolContract :=  {  acc := ·12  }   . 
Global Instance Acc_Ledger_ι_DePool : Accessor Ledger_ι_DePool :=  {  acc := ·13  }   . 
Global Instance Acc_Ledger_ι_Participant : Accessor Ledger_ι_Participant :=  {  acc := ·14  }   . 
Global Instance Acc_Ledger_ι_TestElector : Accessor Ledger_ι_TestElector :=  {  acc := ·15  }   . 
Global Instance Acc_Ledger_ι_VMState : Accessor Ledger_ι_VMState :=  {  acc := ·16  }   . 
Global Instance Acc_Ledger_ι_LocalState : Accessor Ledger_ι_LocalState :=  {  acc := ·17  }   . 
Instance Ledger_default : XDefault Ledger :=  {  
 	 default := LedgerC default default default default default default default default default default default default default default default default default default  
  }   . 
Definition LedgerT := StateT Ledger .  
 

(* 1 *)
(*embeddedType for all Accessors *)
Definition projEmbed_Accessor {U T}{f: T -> U}`{s: Struct T}`{a: @Accessor T U s f}: T -> U := f.
Definition injEmbed_Accessor {U T}{f: T -> U}`{s: Struct T}`{a: @Accessor T U s f} (x: U) (t: T): T :=
{$ t with f := x $}.

 
 Definition T1 := DebugDePool . 
 Definition T2 := ValidatorBase . 
 Definition T3 := ParticipantBase . 
 Definition T4 := DePoolHelper . 
 Definition T5 := Errors . 
 Definition T6 := InternalErrors . 
 Definition T7 := DePoolLib . 
 Definition T8 := DePoolProxyContract . 
 Definition T9 := DePoolContract . 
 Definition T10 := TestElector . 
 Definition T11 := VMState . 
 Definition T12 := LocalState . 
 
 
 Definition projEmbed_T1 : Ledger -> T1 := projEmbed_Accessor . 
 Definition injEmbed_T1 : T1 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T1 : forall ( t : T1 ) ( s : Ledger ) , 
 projEmbed_T1 ( injEmbed_T1 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T1 : forall ( s : Ledger ) , injEmbed_T1 ( projEmbed_T1 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T1 : forall ( t1 t2 : T1 ) ( s : Ledger ) , 
 injEmbed_T1 t1 ( injEmbed_T1 t2 s) = 
 injEmbed_T1 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT1 : EmbeddedType Ledger T1 := 
 {
 projEmbed := projEmbed_T1 ; 
 injEmbed := injEmbed_T1 ; 
 projinj := projinj_T1 ; 
 injproj := injproj_T1 ; 
 injinj  := injinj_T1 ; 
 } . 
 
 
 
 Definition projEmbed_T2 : Ledger -> T2 := projEmbed_Accessor . 
 Definition injEmbed_T2 : T2 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T2 : forall ( t : T2 ) ( s : Ledger ) , 
 projEmbed_T2 ( injEmbed_T2 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T2 : forall ( s : Ledger ) , injEmbed_T2 ( projEmbed_T2 s ) s = s . Proof.
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
 
 Lemma injproj_T3 : forall ( s : Ledger ) , injEmbed_T3 ( projEmbed_T3 s ) s = s . Proof.
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
 
 
 
 Definition projEmbed_T4 : Ledger -> T4 := projEmbed_Accessor . 
 Definition injEmbed_T4 : T4 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T4 : forall ( t : T4 ) ( s : Ledger ) , 
 projEmbed_T4 ( injEmbed_T4 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T4 : forall ( s : Ledger ) , injEmbed_T4 ( projEmbed_T4 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T4 : forall ( t1 t2 : T4 ) ( s : Ledger ) , 
 injEmbed_T4 t1 ( injEmbed_T4 t2 s) = 
 injEmbed_T4 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT4 : EmbeddedType Ledger T4 := 
 {
 projEmbed := projEmbed_T4 ; 
 injEmbed := injEmbed_T4 ; 
 projinj := projinj_T4 ; 
 injproj := injproj_T4 ; 
 injinj  := injinj_T4 ; 
 } . 
 
 
 
 Definition projEmbed_T5 : Ledger -> T5 := projEmbed_Accessor . 
 Definition injEmbed_T5 : T5 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T5 : forall ( t : T5 ) ( s : Ledger ) , 
 projEmbed_T5 ( injEmbed_T5 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T5 : forall ( s : Ledger ) , injEmbed_T5 ( projEmbed_T5 s ) s = s . Proof.
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
 
 
 
 Definition projEmbed_T6 : Ledger -> T6 := projEmbed_Accessor . 
 Definition injEmbed_T6 : T6 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T6 : forall ( t : T6 ) ( s : Ledger ) , 
 projEmbed_T6 ( injEmbed_T6 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T6 : forall ( s : Ledger ) , injEmbed_T6 ( projEmbed_T6 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T6 : forall ( t1 t2 : T6 ) ( s : Ledger ) , 
 injEmbed_T6 t1 ( injEmbed_T6 t2 s) = 
 injEmbed_T6 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT6 : EmbeddedType Ledger T6 := 
 {
 projEmbed := projEmbed_T6 ; 
 injEmbed := injEmbed_T6 ; 
 projinj := projinj_T6 ; 
 injproj := injproj_T6 ; 
 injinj  := injinj_T6 ; 
 } . 
 
 
 
 Definition projEmbed_T7 : Ledger -> T7 := projEmbed_Accessor . 
 Definition injEmbed_T7 : T7 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T7 : forall ( t : T7 ) ( s : Ledger ) , 
 projEmbed_T7 ( injEmbed_T7 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T7 : forall ( s : Ledger ) , injEmbed_T7 ( projEmbed_T7 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T7 : forall ( t1 t2 : T7 ) ( s : Ledger ) , 
 injEmbed_T7 t1 ( injEmbed_T7 t2 s) = 
 injEmbed_T7 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT7 : EmbeddedType Ledger T7 := 
 {
 projEmbed := projEmbed_T7 ; 
 injEmbed := injEmbed_T7 ; 
 projinj := projinj_T7 ; 
 injproj := injproj_T7 ; 
 injinj  := injinj_T7 ; 
 } . 
 
 
 
 Definition projEmbed_T8 : Ledger -> T8 := projEmbed_Accessor . 
 Definition injEmbed_T8 : T8 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T8 : forall ( t : T8 ) ( s : Ledger ) , 
 projEmbed_T8 ( injEmbed_T8 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T8 : forall ( s : Ledger ) , injEmbed_T8 ( projEmbed_T8 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T8 : forall ( t1 t2 : T8 ) ( s : Ledger ) , 
 injEmbed_T8 t1 ( injEmbed_T8 t2 s) = 
 injEmbed_T8 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT8 : EmbeddedType Ledger T8 := 
 {
 projEmbed := projEmbed_T8 ; 
 injEmbed := injEmbed_T8 ; 
 projinj := projinj_T8 ; 
 injproj := injproj_T8 ; 
 injinj  := injinj_T8 ; 
 } . 
 
 
 
 Definition projEmbed_T9 : Ledger -> T9 := projEmbed_Accessor . 
 Definition injEmbed_T9 : T9 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T9 : forall ( t : T9 ) ( s : Ledger ) , 
 projEmbed_T9 ( injEmbed_T9 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T9 : forall ( s : Ledger ) , injEmbed_T9 ( projEmbed_T9 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T9 : forall ( t1 t2 : T9 ) ( s : Ledger ) , 
 injEmbed_T9 t1 ( injEmbed_T9 t2 s) = 
 injEmbed_T9 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT9 : EmbeddedType Ledger T9 := 
 {
 projEmbed := projEmbed_T9 ; 
 injEmbed := injEmbed_T9 ; 
 projinj := projinj_T9 ; 
 injproj := injproj_T9 ; 
 injinj  := injinj_T9 ; 
 } . 
 
 
 
 Definition projEmbed_T10 : Ledger -> T10 := projEmbed_Accessor . 
 Definition injEmbed_T10 : T10 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T10 : forall ( t : T10 ) ( s : Ledger ) , 
 projEmbed_T10 ( injEmbed_T10 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T10 : forall ( s : Ledger ) , injEmbed_T10 ( projEmbed_T10 s ) s = s . Proof.
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
 
Lemma injcommute_T1_T2: forall  (u:T2) (t:T1)  (s:Ledger), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1_T2: 
         @InjectCommutableStates Ledger T1 T2 
               := 
{
  injcommute := injcommute_T1_T2
}.
Definition embeddedProduct_T1_T2 := 
           @embeddedProduct Ledger T1 T2 
                 InjectCommutableStates_T1_T2.
Existing Instance embeddedProduct_T1_T2.
 
Lemma injcommute_T1xT2_T3: 
               forall ( u : T3 ) ( t :  T1 * T2  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2_T3 : 
@InjectCommutableStates Ledger (  T1 * T2  ) T3 := 
{
  injcommute := injcommute_T1xT2_T3 
}.

Definition embeddedProduct_T1xT2_T3 := 
           @embeddedProduct Ledger (  T1 * T2  ) T3
  
           InjectCommutableStates_T1xT2_T3.

Existing Instance embeddedProduct_T1xT2_T3 .
 
Lemma injcommute_T1xT2xT3_T4: 
               forall ( u : T4 ) ( t :  T1 * T2 * T3  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3_T4 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3  ) T4 := 
{
  injcommute := injcommute_T1xT2xT3_T4 
}.

Definition embeddedProduct_T1xT2xT3_T4 := 
           @embeddedProduct Ledger (  T1 * T2 * T3  ) T4
  
           InjectCommutableStates_T1xT2xT3_T4.

Existing Instance embeddedProduct_T1xT2xT3_T4 .
 
Lemma injcommute_T1xT2xT3xT4_T5: 
               forall ( u : T5 ) ( t :  T1 * T2 * T3 * T4  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4_T5 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4  ) T5 := 
{
  injcommute := injcommute_T1xT2xT3xT4_T5 
}.

Definition embeddedProduct_T1xT2xT3xT4_T5 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4  ) T5
  
           InjectCommutableStates_T1xT2xT3xT4_T5.

Existing Instance embeddedProduct_T1xT2xT3xT4_T5 .
 
Lemma injcommute_T1xT2xT3xT4xT5_T6: 
               forall ( u : T6 ) ( t :  T1 * T2 * T3 * T4 * T5  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5_T6 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5  ) T6 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5_T6 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5_T6 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5  ) T6
  
           InjectCommutableStates_T1xT2xT3xT4xT5_T6.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5_T6 .
 
Lemma injcommute_T1xT2xT3xT4xT5xT6_T7: 
               forall ( u : T7 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6_T7 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6  ) T7 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5xT6_T7 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6_T7 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6  ) T7
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6_T7.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6_T7 .
 
Lemma injcommute_T1xT2xT3xT4xT5xT6xT7_T8: 
               forall ( u : T8 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6 * T7  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7_T8 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7  ) T8 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5xT6xT7_T8 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7_T8 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7  ) T8
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7_T8.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7_T8 .
 
Lemma injcommute_T1xT2xT3xT4xT5xT6xT7xT8_T9: 
               forall ( u : T9 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8_T9 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8  ) T9 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5xT6xT7xT8_T9 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8_T9 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8  ) T9
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8_T9.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8_T9 .
 
Lemma injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10: 
               forall ( u : T10 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9  ) T10 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9  ) T10
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 .
 
Lemma injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11: 
               forall ( u : T11 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10  ) T11 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10  ) T11
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11 .
 
Lemma injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12: 
               forall ( u : T12 ) ( t :  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11  ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11  ) T12 := 
{
  injcommute := injcommute_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 := 
           @embeddedProduct Ledger (  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11  ) T12
  
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 .
 
Axiom fullState_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 : forall s s0, 
      injEmbed ( T:=(  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11  ) ) 
(projEmbed s) (injEmbed (T:= T12 ) (projEmbed s) s0) = s.
(* Lemma fullState_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 : forall s s0, 
      injEmbed ( T:=(  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11  ) ) 
(projEmbed s) (injEmbed (T:= T12 ) (projEmbed s) s0) = s.
Proof.
  intros. compute. destruct s.
  auto.
Qed. *)

Instance FullState_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 : 
         FullState Ledger ( T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11  ) T12 := 
{
  injComm := InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 ;
  fullState := fullState_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 
}. 
Notation "'↑12' m":= (liftEmbeddedState ( T := T12 ) m ) (at level 10, left associativity): solidity_scope. 
Notation "'↑11' m":= (liftEmbeddedState ( T := T11 ) m ) (at level 10, left associativity): solidity_scope. 
Notation "'↑10' m":= (liftEmbeddedState ( T := T10 ) m ) (at level 10, left associativity): solidity_scope. 
Notation "'↑9' m":= (liftEmbeddedState ( T := T9 ) m ) (at level 10, left associativity): solidity_scope. 
Notation "'↑8' m":= (liftEmbeddedState ( T := T8 ) m ) (at level 10, left associativity): solidity_scope. 
Notation "'↑7' m":= (liftEmbeddedState ( T := T7 ) m ) (at level 10, left associativity): solidity_scope. 
Notation "'↑6' m":= (liftEmbeddedState ( T := T6 ) m ) (at level 10, left associativity): solidity_scope. 
Notation "'↑5' m":= (liftEmbeddedState ( T := T5 ) m ) (at level 10, left associativity): solidity_scope. 
Notation "'↑4' m":= (liftEmbeddedState ( T := T4 ) m ) (at level 10, left associativity): solidity_scope. 
Notation "'↑3' m":= (liftEmbeddedState ( T := T3 ) m ) (at level 10, left associativity): solidity_scope. 
Notation "'↑2' m":= (liftEmbeddedState ( T := T2 ) m ) (at level 10, left associativity): solidity_scope. 
Notation "'↑1' m":= (liftEmbeddedState ( T := T1 ) m ) (at level 10, left associativity): solidity_scope. 
Notation " '↑0' m " := (liftEmbeddedState ( T :=  T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11  ) m ) (at level 10, left associativity): solidity_scope. 
 
 Notation " '↑↑1' n '^^' m " := ( do a ← (↑3 n  ) ; return! ( m a )  )%sol(at level 10, left associativity): solidity_scope.

End LedgerClass .
