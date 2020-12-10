
type __ = Obj.t

type nat =
| O
| S of nat

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : nat -> nat -> nat

val sub : nat -> nat -> nat

val divmod : nat -> nat -> nat -> nat -> nat * nat

val div : nat -> nat -> nat

val modulo : nat -> nat -> nat

module Nat :
 sig
  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool
 end

val hd_error : 'a1 list -> 'a1 option

val tl : 'a1 list -> 'a1 list

val concat : 'a1 list list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

type t =
| New

type command = __

type answer = __

type 'x t0 =
| Ret of 'x
| Call of command
| Let of __ t0 * (__ -> 'x t0)
| Choose of 'x t0 * 'x t0
| Join of __ t0 * __ t0

module Notations :
 sig
  val ret : t -> 'a1 -> 'a1 t0

  val call : t -> command -> answer t0
 end

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val eqb : positive -> positive -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat
 end

module N :
 sig
  val add : n -> n -> n

  val mul : n -> n -> n

  val to_nat : n -> nat
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val eqb : z -> z -> bool
 end

val n_of_digits : bool list -> n

val n_of_ascii : char -> n

val nat_of_ascii : char -> nat

val string_dec : char list -> char list -> bool

val eqb0 : char list -> char list -> bool

val append : char list -> char list -> char list

val length0 : char list -> nat

val substring : nat -> nat -> char list -> char list

val prefix : char list -> char list -> bool

val index : nat -> char list -> char list -> nat option

type t1 = char list

module Option :
 sig
  val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option
 end

module LString :
 sig
  val of_string : char list -> t1

  val s : char list -> t1

  type t = char list

  module Char :
   sig
    val n : char
   end
 end

type t2 =
| ListFiles of LString.t
| ReadFile of LString.t
| WriteFile of LString.t * LString.t
| DeleteFile of LString.t
| System of LString.t
| Eval of LString.t list
| Print of LString.t
| ReadLine

val effect : t

val read_file : LString.t -> LString.t option t0

val printl : LString.t -> bool t0

val log : LString.t -> unit t0

val apply : ('a1 -> 'a2) -> 'a1 -> 'a2

module BigInt :
 sig
  type t = Big_int.big_int

  val to_Z_aux :
    t -> 'a1 -> ('a2 -> 'a1) -> ('a2 -> 'a1) -> 'a2 -> ('a2 -> 'a2) -> ('a2
    -> 'a2) -> 'a1

  val to_Z : t -> z
 end

module String :
 sig
  type t = string

  val of_lstring : LString.t -> t

  val to_lstring : t -> LString.t
 end

module Sys :
 sig
  val argv : String.t list
 end

module Lwt :
 sig
  type 'a t = 'a Lwt.t

  val ret : 'a1 -> 'a1 t

  val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t

  val join : 'a1 t -> 'a2 t -> ('a1 * 'a2) t

  val choose : 'a1 t -> 'a1 t -> 'a1 t

  val launch : 'a1 t -> 'a1

  val list_files : String.t -> String.t list option t

  val read_file : String.t -> String.t option t

  val write_file : String.t -> String.t -> bool t

  val delete_file : String.t -> bool t

  val system : String.t -> bool option t

  val eval : String.t list -> ((BigInt.t * String.t) * String.t) option t

  val print : String.t -> bool t

  val read_line : unit -> String.t option t
 end

val eval_command : command -> answer Lwt.t

val eval0 : 'a1 t0 -> 'a1 Lwt.t

val launch0 : (LString.t list -> unit t0) -> unit

val natToDigit : nat -> char list

val writeNatAux : nat -> nat -> char list -> char list

val writeNat : nat -> char list

val split_string' : char list -> char list -> nat -> char list list

val split_string : char list -> char list -> char list list

val concat_with : char list -> char list list -> char list

val newline : char list

val tab : char list

val separators : char list list

val add_exist_types : char list list -> char list list

val first2 : char list -> char list

val first4 : char list -> char list

val is_num_this_string' : char list -> bool

val is_num_this_string : char list -> bool

val isNum : char list -> bool

val have_it_symbol : char -> char list -> bool

val split_string'0 : char list -> char list -> char list list

val t2str : LString.t -> char list

val clearComment : bool -> char list -> char list

val clearComment1 : bool -> char list -> char list

val test_already_exists : char list -> char list list -> bool

val test_not_already_exists_for_list :
  char list list -> char list list -> bool

val deleteComment : char list list list -> char list list list

val headS : 'a1 -> 'a1 list -> 'a1

val clear_string_easy : char list list -> char list list

val clear_list_easy : char list list list -> char list list list

val last_delete : 'a1 list -> 'a1 list

val constructor_function : nat -> char list list -> char list list

val pulling_list_elements : char list -> char list list -> char list list

val find_typelist :
  (char list * char list list) list -> char list -> char list list

val newstringing_for_length : nat -> char list list -> char list list

val find_brace_interior : z -> char list list -> char list list

val find_braket_interior : z -> char list list -> char list list

val find_crotch_interior : bool -> char list list -> char list list

val what_is_next : char list list -> char list

val setSpace : char list -> char list

val concat_sq_brakets : char list list -> char list list

val sol_types2coq_mini_types : char list -> char list

val del_lead_2_symbols_UU03b9__ : char list -> char list

val cot_mini_types2coq_types : char list -> char list

val sol2coq_full_types : char list -> char list

val all_end_prepare : char list list -> char list list

val prepare_easy_funcs : char list list -> char list list

val uppers : char list list

val dotted_prepare : char list list -> char list list

val get_type_line : char list list -> char list list

val get_type_line' :
  char list -> char list list -> (char list * char list) list

val get_type_lines :
  char list -> char list list -> (char list * char list) list

val get_require_body : bool -> char list list -> char list list

val get_list_modifier :
  char list -> char list list -> char list * char list list

val modifier_list_with_bodies :
  char list list -> (char list * char list list) list

val make_function_returns : char list list -> char list list

val get_function_returns : char list -> char list list -> char list list

val make_function_interior :
  char list -> char list -> char list list -> char list list

val get_function : char list -> char list list -> char list list

val make_functions' : char list -> char list list -> char list list list

val get_argum : char list list -> char list list

val get_full_function : char list -> char list list -> char list list

val make_functions : char list -> char list list -> char list list list

val get_modif_from_list :
  (char list * char list list) list -> char list -> char list list

val add_modifiers_to_functions' :
  (char list * char list list) list -> char list list -> char list list

val add_modifiers_to_functions : char list list -> char list list

val get_orig_text_funcs_list :
  char list -> char list list -> (char list * char list list) list

val add_orig_funcs_texts :
  (char list * char list list) list -> char list list list -> char list list
  list

val get_digits_list' : char list list -> char list list -> char list list

val get_parameters_throw_digit : nat -> char list list -> char list

val toPureDigit : char list -> char list

val get_definition_throw_digit : char list list -> char list

val get_digits_list : char list list list -> char list

val make_tuple_braket : char list list -> char list list

val analisys_for_returns' : char list list -> char list list

val analisys_for_returns : char list list -> char list list

val repair_require : char list list -> char list list

val set_return_I : char list list -> char list list

val repair_return : char list list -> char list list

val make_struct_interior : char list -> char list list -> char list list

val get_struct_itself :
  char list -> char list list -> (char list * char list) list

val get_struct_var_list :
  char list -> char list list -> (char list * char list) list

val make_structs_var_list :
  char list -> char list list -> (char list * char list) list list

val make_list_level_0 : bool -> nat -> char list list -> char list list

val make_elses' : char list -> char list list -> (char list * char list) list

val make_elses_var_list :
  char list -> char list list -> (char list * char list) list

val make_contract_interior_v :
  char list -> char list list -> (char list * char list) list

val get_contract_v : char list list -> (char list * char list) list

val make_contracts_v : char list list -> (char list * char list) list list

val make_contract_interior :
  char list -> char list list -> char list list list

val get_contract : char list list -> char list list list

val make_contracts : char list list -> char list list list list

val structs_list : char list -> char list list -> (char list * char list) list

val const_list : char list -> char list list -> (char list * char list) list

val functions_list' :
  char list -> char list list -> (char list * char list) list

val functions_list :
  char list -> char list list -> (char list * char list) list

val get_list_executing_functions : char list list -> char list list

val func_exchange :
  char list list list -> char list list -> char list list list

val rigth_order_funcs :
  char list list -> char list list list -> char list list list -> char list
  list list

val find_coq_name : char list -> (char list * char list) list -> char list

val find_coq_name2 : char list -> (char list * char list) list -> char list

val rename_sol2coq1 :
  char list -> (char list * char list) list -> char list list -> char list
  list

val rename_sol2coq :
  (char list * char list) list -> char list list -> char list list

val get_local_vars_list : char list list -> char list list

val get_list_funcs_args : char list list -> char list list

val get_list_vars_function : char list list -> char list list

val m_renaming :
  (char list * char list) list -> char list list -> char list list

val else_renaming :
  (char list * char list) list -> char list list -> char list list

val prepare_function_type_var : char list list -> char list list

val delete_mapping : bool -> char list list -> char list list

val rename_numbers : char list list -> char list list

val rename_tvm_some : char list list -> char list list

val clean_vars_list :
  (char list * char list) list -> (char list * char list) list

val get_list_func_type' : bool -> char list list -> char list list

val get_list_func_type :
  char list list list -> (char list * char list list) list

val clear_list_func_type : char list list list -> char list list list

val adding : (char list * char list list) list -> char list -> char list list

val add_list_func_type'' :
  char list -> (char list * char list list) list -> char list list ->
  char list list

val add_list_func_type' :
  (char list * char list list) list -> char list list -> char list list

val add_list_func_type : char list list list -> char list list list

val numering_not_empty_contracts :
  nat -> char list list -> (char list * char list) list

val get_number_contract_vars :
  char list -> char list list -> (char list * char list) list

val numering_contract_vars' : char list list -> (char list * char list) list

val plust_tuple :
  nat -> (char list * char list) list -> (char list * char list) list

val numering_contract_vars : char list list -> (char list * char list) list

type type_of_name =
| NUMBER
| LOCAL
| VAR
| FUNf
| NOTHING

val who : char list -> type_of_name

val renaming_local_vars' : char list list -> char list list -> char list list

val renaming_local_vars : char list list -> char list list

val back_local_vars : char list list -> char list list

val concat_op_equ : char list list -> char list list -> char list list

val isElse : char list list -> bool

val array_2_mapping : char list list -> char list list

val get_to_sol :
  (char list * char list) list -> char list list -> char list list ->
  char list list -> char list list

val if_who : type_of_name -> type_of_name -> bool

val work_operations : char list list -> char list list

val get_first_symbols_to_ : char list -> char list

val add_lift_to_vars :
  (char list * char list) list -> char list list -> char list list

val split_iterior_members_list : char list list -> char list list

val is_msg_point : char list -> char list list -> bool

val repair_msg_point : char list -> char list list -> char list list

val delete_some : char list list -> char list list

val header : char list

val footer : char list

val prepare_tuple :
  (char list * char list) list -> (char list * char list) list

val get_list_of_tuple :
  ((char list * nat) * char list list) list -> char list list

val delete_double_functions :
  ((char list * nat) * char list list) list -> char list list list ->
  char list list list

val interface_list : char list list -> char list list

val library_list : char list list -> char list list

val interface_prepare :
  bool -> char list list -> char list list -> char list list

val shaper : char list -> char list

val translator : LString.t list -> unit t0

val main : unit
