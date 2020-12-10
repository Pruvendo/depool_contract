Fixpoint set_compare_lt(sl:list string) :=
match sl with
| nil => nil
(* 44 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"<" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "[":: n :: "]" ::"<44" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_compare_lt t
(* 43 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"<" :: h3 :: "^^" :: h4 :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"<43" :: h3 :: "^^" :: h4 :: set_compare_lt t
(* 45 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"<" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"<45" :: h3 :: "[":: m :: "]" :: set_compare_lt t
(* 4 *)
| h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "<" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "<40" :: "$" :: h3 :: set_compare_lt t
                          | LOCAL  => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "<41" :: h3 :: set_compare_lt t
                          | VAR    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "<42" :: h3 :: set_compare_lt t
                          | FUNf    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "<46" :: h3 :: set_compare_lt t
                          | _ => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "<" :: h3 :: set_compare_lt t
                          end else h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "<" :: h3 :: set_compare_lt t

(* 34 *)
| h1 :: "^^" :: h2 :: "<" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "<34" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_compare_lt t
(* 33 *)
| h1 :: "^^" :: h2 :: "<" :: h3 :: "^^" :: h4 :: t =>
                           h1 :: "^^" :: h2 :: "<33" :: h3 :: "^^" :: h4 :: set_compare_lt t
(* 35 *)
| h1 :: "^^" :: h2 :: "<" :: h3 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "<35" :: h3 :: "[":: m :: "]" :: set_compare_lt t
(* 3 *)
| h1 :: "^^" :: h2 :: "<" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "<30" :: "$" :: h3 :: set_compare_lt t
                          | LOCAL  => h1 :: "^^" :: h2 :: "<31" :: h3 :: set_compare_lt t
                          | VAR    => h1 :: "^^" :: h2 :: "<32" :: h3 :: set_compare_lt t
                          | FUNf    => h1 :: "^^" :: h2 :: "<36" :: h3 :: set_compare_lt t
                          | _ => h1 :: "^^" :: h2 :: "<" :: h3 :: set_compare_lt t
                          end else h1 :: "^^" :: h2 :: "<" :: h3 :: set_compare_lt t
(* 54 *)
| h1 :: "[" :: n :: "]" :: "<" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "[" :: n :: "]" :: "<54" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: set_compare_lt t
(* 53 *)
| h1 :: "[":: n :: "]" :: "<" :: h2 :: "^^" :: h3 :: t =>
                          h1 :: "[":: n :: "]" :: "<53" :: h2 :: "^^" :: h3 :: set_compare_lt t
(* 55 *)
| h1 :: "[":: n :: "]" :: "<" :: h2 :: "[":: m :: "]" :: t =>
                    h1 :: "[":: n :: "]" :: "<55" :: h2 :: "[":: m :: "]" :: set_compare_lt t
(* 2 *)
| h1 :: "[" :: n :: "]" :: "<" :: h2 :: t => if ( if_who (who h1) VAR ) then
                          match who h2 with
                          | NUMBER => h1 :: "[" :: n :: "]" :: "<50" :: "$" :: h2 :: set_compare_lt t
                          | LOCAL  => h1 :: "[" :: n :: "]" :: "<51" :: h2 :: set_compare_lt t
                          | VAR    => h1 :: "[" :: n :: "]" :: "<52" :: h2 :: set_compare_lt t
                          | FUNf    => h1 :: "[" :: n :: "]" :: "<56" :: h2 :: set_compare_lt t
                          | _ => h1 :: "[" :: n :: "]" :: "<" :: h2 :: set_compare_lt t
                          end else h1 :: "[" :: n :: "]" :: "<" :: h2 :: set_compare_lt t
(* 6 *)
| h1 :: "<" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "<04" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_lt t
                          | LOCAL  => h1 :: "<14" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_lt t
                          | VAR    => h1 :: "<24" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_lt t
                          | FUNf    => h1 :: "<64" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_lt t
                          | _ => h1 :: "<" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_lt t
                          end
(* 5 *)
| h1 :: "<" :: h2 :: "^^" :: h3 :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "<03" :: h2 :: "^^" :: h3 :: set_compare_lt t
                          | LOCAL  => h1 :: "<13" :: h2 :: "^^" :: h3 :: set_compare_lt t
                          | VAR    => h1 :: "<23" :: h2 :: "^^" :: h3 :: set_compare_lt t
                          | FUNf    => h1 :: "<63" :: h2 :: "^^" :: h3 :: set_compare_lt t
                          | _ => h1 :: "<" :: h2 :: "^^" :: h3 :: set_compare_lt t
                          end
(* 7 *)
| h1 :: "<" :: h2 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "<05" :: h2 :: "[":: n :: "]" :: set_compare_lt t
                          | LOCAL  => h1 :: "<15" :: h2 :: "[":: n :: "]" :: set_compare_lt t
                          | VAR    => h1 :: "<25" :: h2 :: "[":: n :: "]" :: set_compare_lt t
                          | FUNf    => h1 :: "<65" :: h2 :: "[":: n :: "]" :: set_compare_lt t
                          | _ => h1 :: "<" :: h2 :: "[":: n :: "]" :: set_compare_lt t
                          end
(* 1 *)
| h1 :: "<" :: h2 :: t => match who h1, who h2 with
                          | NUMBER, NUMBER => "$" :: h1 :: "<00" :: "$" :: h2 :: set_compare_lt t
                          | NUMBER, LOCAL  => "$" :: h1 :: "<01" :: h2 :: set_compare_lt t
                          | NUMBER, VAR    => "$" :: h1 :: "<02" :: h2 :: set_compare_lt t
                          | NUMBER, FUNf   => "$" :: h1 :: "<06" :: h2 :: set_compare_lt t
                          | LOCAL, NUMBER => h1 :: "<10" :: "$" :: h2 :: set_compare_lt t
                          | LOCAL, LOCAL  => h1 :: "<11" :: h2 :: set_compare_lt t
                          | LOCAL, VAR    => h1 :: "<12" :: h2 :: set_compare_lt t
                          | LOCAL, FUNf   => h1 :: "<16" :: h2 :: set_compare_lt t
                          | VAR,   NUMBER => h1 :: "<20" :: h2 :: set_compare_lt t   
                          | VAR,   LOCAL  => h1 :: "<21" :: h2 :: set_compare_lt t
                          | VAR,   VAR    => h1 :: "<22" :: h2 :: set_compare_lt t
                          | VAR,   FUNf   => h1 :: "<20" :: h2 :: set_compare_lt t
                          | FUNf,  NUMBER => h1 :: "<60" :: "$" :: h2 :: set_compare_lt t   
                          | FUNf,   LOCAL  => h1 :: "<61" :: h2 :: set_compare_lt t
                          | FUNf,   VAR    => h1 :: "<62" :: h2 :: set_compare_lt t
                          | FUNf,   FUNf   => h1 :: "<66" :: h2 :: set_compare_lt t
                          | _, _ => h1 :: "<" :: h2 :: set_compare_lt t
                          end
| h :: t => h :: set_compare_lt t
end.

Fixpoint set_compare_le(sl:list string) :=
match sl with
| nil => nil
(* 44 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"<=" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "[":: n :: "]" ::"<=44" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_compare_le t
(* 43 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"<=" :: h3 :: "^^" :: h4 :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"<=43" :: h3 :: "^^" :: h4 :: set_compare_le t
(* 45 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"<=" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"<=45" :: h3 :: "[":: m :: "]" :: set_compare_le t
(* 4 *)
| h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "<=" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "<=40" :: "$" :: h3 :: set_compare_le t
                          | LOCAL  => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "<=41" :: h3 :: set_compare_le t
                          | VAR    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "<=42" :: h3 :: set_compare_le t
                          | FUNf    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "<=46" :: h3 :: set_compare_le t
                          | _ => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "<=" :: h3 :: set_compare_le t
                          end else h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "<=" :: h3 :: set_compare_le t

(* 34 *)
| h1 :: "^^" :: h2 :: "<=" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "<=34" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_compare_le t
(* 33 *)
| h1 :: "^^" :: h2 :: "<=" :: h3 :: "^^" :: h4 :: t =>
                           h1 :: "^^" :: h2 :: "<=33" :: h3 :: "^^" :: h4 :: set_compare_le t
(* 35 *)
| h1 :: "^^" :: h2 :: "<=" :: h3 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "<=35" :: h3 :: "[":: m :: "]" :: set_compare_le t
(* 3 *)
| h1 :: "^^" :: h2 :: "<=" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "<=30" :: "$" :: h3 :: set_compare_le t
                          | LOCAL  => h1 :: "^^" :: h2 :: "<=31" :: h3 :: set_compare_le t
                          | VAR    => h1 :: "^^" :: h2 :: "<=32" :: h3 :: set_compare_le t
                          | FUNf    => h1 :: "^^" :: h2 :: "<=36" :: h3 :: set_compare_le t
                          | _ => h1 :: "^^" :: h2 :: "<=" :: h3 :: set_compare_le t
                          end else h1 :: "^^" :: h2 :: "<=" :: h3 :: set_compare_le t
(* 54 *)
| h1 :: "[" :: n :: "]" :: "<=" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "[" :: n :: "]" :: "<=54" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: set_compare_le t
(* 53 *)
| h1 :: "[":: n :: "]" :: "<=" :: h2 :: "^^" :: h3 :: t =>
                          h1 :: "[":: n :: "]" :: "<=53" :: h2 :: "^^" :: h3 :: set_compare_le t
(* 55 *)
| h1 :: "[":: n :: "]" :: "<=" :: h2 :: "[":: m :: "]" :: t =>
                    h1 :: "[":: n :: "]" :: "<=55" :: h2 :: "[":: m :: "]" :: set_compare_le t
(* 2 *)
| h1 :: "[" :: n :: "]" :: "<=" :: h2 :: t => if ( if_who (who h1) VAR ) then
                          match who h2 with
                          | NUMBER => h1 :: "[" :: n :: "]" :: "<=50" :: "$" :: h2 :: set_compare_le t
                          | LOCAL  => h1 :: "[" :: n :: "]" :: "<=51" :: h2 :: set_compare_le t
                          | VAR    => h1 :: "[" :: n :: "]" :: "<=52" :: h2 :: set_compare_le t
                          | FUNf    => h1 :: "[" :: n :: "]" :: "<=56" :: h2 :: set_compare_le t
                          | _ => h1 :: "[" :: n :: "]" :: "<=" :: h2 :: set_compare_le t
                          end else h1 :: "[" :: n :: "]" :: "<=" :: h2 :: set_compare_le t
(* 6 *)
| h1 :: "<=" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "<=04" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_le t
                          | LOCAL  => h1 :: "<=14" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_le t
                          | VAR    => h1 :: "<=24" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_le t
                          | FUNf    => h1 :: "<=64" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_le t
                          | _ => h1 :: "<=" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_le t
                          end
(* 5 *)
| h1 :: "<=" :: h2 :: "^^" :: h3 :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "<=03" :: h2 :: "^^" :: h3 :: set_compare_le t
                          | LOCAL  => h1 :: "<=13" :: h2 :: "^^" :: h3 :: set_compare_le t
                          | VAR    => h1 :: "<=23" :: h2 :: "^^" :: h3 :: set_compare_le t
                          | FUNf    => h1 :: "<=63" :: h2 :: "^^" :: h3 :: set_compare_le t
                          | _ => h1 :: "<=" :: h2 :: "^^" :: h3 :: set_compare_le t
                          end
(* 7 *)
| h1 :: "<=" :: h2 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "<=05" :: h2 :: "[":: n :: "]" :: set_compare_le t
                          | LOCAL  => h1 :: "<=15" :: h2 :: "[":: n :: "]" :: set_compare_le t
                          | VAR    => h1 :: "<=25" :: h2 :: "[":: n :: "]" :: set_compare_le t
                          | FUNf    => h1 :: "<=65" :: h2 :: "[":: n :: "]" :: set_compare_le t
                          | _ => h1 :: "<=" :: h2 :: "[":: n :: "]" :: set_compare_le t
                          end
(* 1 *)
| h1 :: "<=" :: h2 :: t => match who h1, who h2 with
                          | NUMBER, NUMBER => "$" :: h1 :: "<=00" :: "$" :: h2 :: set_compare_le t
                          | NUMBER, LOCAL  => "$" :: h1 :: "<=01" :: h2 :: set_compare_le t
                          | NUMBER, VAR    => "$" :: h1 :: "<=02" :: h2 :: set_compare_le t
                          | NUMBER, FUNf   => "$" :: h1 :: "<=06" :: h2 :: set_compare_le t
                          | LOCAL, NUMBER => h1 :: "<=10" :: "$" :: h2 :: set_compare_le t
                          | LOCAL, LOCAL  => h1 :: "<=11" :: h2 :: set_compare_le t
                          | LOCAL, VAR    => h1 :: "<=12" :: h2 :: set_compare_le t
                          | LOCAL, FUNf   => h1 :: "<=16" :: h2 :: set_compare_le t
                          | VAR,   NUMBER => h1 :: "<=20" :: "$" :: h2 :: set_compare_le t   
                          | VAR,   LOCAL  => h1 :: "<=21" :: h2 :: set_compare_le t
                          | VAR,   VAR    => h1 :: "<=22" :: h2 :: set_compare_le t
                          | VAR,   FUNf   => h1 :: "<=26" :: h2 :: set_compare_le t
                          | FUNf,  NUMBER => h1 :: "<=60" :: "$" :: h2 :: set_compare_le t   
                          | FUNf,   LOCAL  => h1 :: "<=61" :: h2 :: set_compare_le t
                          | FUNf,   VAR    => h1 :: "<=62" :: h2 :: set_compare_le t
                          | FUNf,   FUNf   => h1 :: "<=66" :: h2 :: set_compare_le t
                          | _, _ => h1 :: "<=" :: h2 :: set_compare_le t
                          end
| h :: t => h :: set_compare_le t
end.

Fixpoint set_compare_ge(sl:list string) :=
match sl with
| nil => nil
(* 44 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::">=" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "[":: n :: "]" ::">=44" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_compare_ge t
(* 43 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::">=" :: h3 :: "^^" :: h4 :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::">=43" :: h3 :: "^^" :: h4 :: set_compare_ge t
(* 45 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::">=" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::">=45" :: h3 :: "[":: m :: "]" :: set_compare_ge t
(* 4 *)
| h1 :: "^^" :: h2 :: "[" :: n :: "]" :: ">=" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: ">=40" :: "$" :: h3 :: set_compare_ge t
                          | LOCAL  => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: ">=41" :: h3 :: set_compare_ge t
                          | VAR    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: ">=42" :: h3 :: set_compare_ge t
                          | FUNf    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: ">=46" :: h3 :: set_compare_ge t
                          | _ => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: ">=" :: h3 :: set_compare_ge t
                          end else h1 :: "^^" :: h2 :: "[" :: n :: "]" :: ">=" :: h3 :: set_compare_ge t

(* 34 *)
| h1 :: "^^" :: h2 :: ">=" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: ">=34" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_compare_ge t
(* 33 *)
| h1 :: "^^" :: h2 :: ">=" :: h3 :: "^^" :: h4 :: t =>
                           h1 :: "^^" :: h2 :: ">=33" :: h3 :: "^^" :: h4 :: set_compare_ge t
(* 35 *)
| h1 :: "^^" :: h2 :: ">=" :: h3 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: ">=35" :: h3 :: "[":: m :: "]" :: set_compare_ge t
(* 3 *)
| h1 :: "^^" :: h2 :: ">=" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: ">=30" :: "$" :: h3 :: set_compare_ge t
                          | LOCAL  => h1 :: "^^" :: h2 :: ">=31" :: h3 :: set_compare_ge t
                          | VAR    => h1 :: "^^" :: h2 :: ">=32" :: h3 :: set_compare_ge t
                          | FUNf    => h1 :: "^^" :: h2 :: ">=36" :: h3 :: set_compare_ge t
                          | _ => h1 :: "^^" :: h2 :: ">=" :: h3 :: set_compare_ge t
                          end else h1 :: "^^" :: h2 :: ">=" :: h3 :: set_compare_ge t
(* 54 *)
| h1 :: "[" :: n :: "]" :: ">=" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "[" :: n :: "]" :: ">=54" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: set_compare_ge t
(* 53 *)
| h1 :: "[":: n :: "]" :: ">=" :: h2 :: "^^" :: h3 :: t =>
                          h1 :: "[":: n :: "]" :: ">=53" :: h2 :: "^^" :: h3 :: set_compare_ge t
(* 55 *)
| h1 :: "[":: n :: "]" :: ">=" :: h2 :: "[":: m :: "]" :: t =>
                    h1 :: "[":: n :: "]" :: ">=55" :: h2 :: "[":: m :: "]" :: set_compare_ge t
(* 2 *)
| h1 :: "[" :: n :: "]" :: ">=" :: h2 :: t => if ( if_who (who h1) VAR ) then
                          match who h2 with
                          | NUMBER => h1 :: "[" :: n :: "]" :: ">=50" :: "$" :: h2 :: set_compare_ge t
                          | LOCAL  => h1 :: "[" :: n :: "]" :: ">=51" :: h2 :: set_compare_ge t
                          | VAR    => h1 :: "[" :: n :: "]" :: ">=52" :: h2 :: set_compare_ge t
                          | FUNf    => h1 :: "[" :: n :: "]" :: ">=56" :: h2 :: set_compare_ge t
                          | _ => h1 :: "[" :: n :: "]" :: ">=" :: h2 :: set_compare_ge t
                          end else h1 :: "[" :: n :: "]" :: ">=" :: h2 :: set_compare_ge t
(* 6 *)
| h1 :: ">=" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: ">=04" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_ge t
                          | LOCAL  => h1 :: ">=14" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_ge t
                          | VAR    => h1 :: ">=24" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_ge t
                          | FUNf    => h1 :: ">=64" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_ge t
                          | _ => h1 :: ">=" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_ge t
                          end
(* 5 *)
| h1 :: ">=" :: h2 :: "^^" :: h3 :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: ">=03" :: h2 :: "^^" :: h3 :: set_compare_ge t
                          | LOCAL  => h1 :: ">=13" :: h2 :: "^^" :: h3 :: set_compare_ge t
                          | VAR    => h1 :: ">=23" :: h2 :: "^^" :: h3 :: set_compare_ge t
                          | FUNf    => h1 :: ">=63" :: h2 :: "^^" :: h3 :: set_compare_ge t
                          | _ => h1 :: ">=" :: h2 :: "^^" :: h3 :: set_compare_ge t
                          end
(* 7 *)
| h1 :: ">=" :: h2 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: ">=05" :: h2 :: "[":: n :: "]" :: set_compare_ge t
                          | LOCAL  => h1 :: ">=15" :: h2 :: "[":: n :: "]" :: set_compare_ge t
                          | VAR    => h1 :: ">=25" :: h2 :: "[":: n :: "]" :: set_compare_ge t
                          | FUNf    => h1 :: ">=65" :: h2 :: "[":: n :: "]" :: set_compare_ge t
                          | _ => h1 :: ">=" :: h2 :: "[":: n :: "]" :: set_compare_ge t
                          end
(* 1 *)
| h1 :: ">=" :: h2 :: t => match who h1, who h2 with
                          | NUMBER, NUMBER => "$" :: h1 :: ">=00" :: "$" :: h2 :: set_compare_ge t
                          | NUMBER, LOCAL  => "$" :: h1 :: ">=01" :: h2 :: set_compare_ge t
                          | NUMBER, VAR    => "$" :: h1 :: ">=02" :: h2 :: set_compare_ge t
                          | NUMBER, FUNf   => "$" :: h1 :: ">=06" :: h2 :: set_compare_ge t
                          | LOCAL, NUMBER => h1 :: ">=10" :: "$" :: h2 :: set_compare_ge t
                          | LOCAL, LOCAL  => h1 :: ">=11" :: h2 :: set_compare_ge t
                          | LOCAL, VAR    => h1 :: ">=12" :: h2 :: set_compare_ge t
                          | LOCAL, FUNf   => h1 :: ">=16" :: h2 :: set_compare_ge t
                          | VAR,   NUMBER => h1 :: ">=20" :: "$" :: h2 :: set_compare_ge t   
                          | VAR,   LOCAL  => h1 :: ">=21" :: h2 :: set_compare_ge t
                          | VAR,   VAR    => h1 :: ">=22" :: h2 :: set_compare_ge t
                          | VAR,   FUNf   => h1 :: ">=26" :: h2 :: set_compare_ge t
                          | FUNf,  NUMBER => h1 :: ">=60" :: "$" :: h2 :: set_compare_ge t   
                          | FUNf,   LOCAL  => h1 :: ">=61" :: h2 :: set_compare_ge t
                          | FUNf,   VAR    => h1 :: ">=62" :: h2 :: set_compare_ge t
                          | FUNf,   FUNf   => h1 :: ">=66" :: h2 :: set_compare_ge t
                          | _, _ => h1 :: ">=" :: h2 :: set_compare_ge t
                          end
| h :: t => h :: set_compare_ge t
end.

Fixpoint set_compare_gt(sl:list string) :=
match sl with
| nil => nil
(* 44 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::">" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "[":: n :: "]" ::">44" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_compare_gt t
(* 43 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::">" :: h3 :: "^^" :: h4 :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::">43" :: h3 :: "^^" :: h4 :: set_compare_gt t
(* 45 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::">" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::">45" :: h3 :: "[":: m :: "]" :: set_compare_gt t
(* 4 *)
| h1 :: "^^" :: h2 :: "[" :: n :: "]" :: ">" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: ">40" :: "$" :: h3 :: set_compare_gt t
                          | LOCAL  => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: ">41" :: h3 :: set_compare_gt t
                          | VAR    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: ">42" :: h3 :: set_compare_gt t
                          | FUNf    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: ">46" :: h3 :: set_compare_gt t
                          | _ => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: ">" :: h3 :: set_compare_gt t
                          end else h1 :: "^^" :: h2 :: "[" :: n :: "]" :: ">" :: h3 :: set_compare_gt t

(* 34 *)
| h1 :: "^^" :: h2 :: ">" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: ">34" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_compare_gt t
(* 33 *)
| h1 :: "^^" :: h2 :: ">" :: h3 :: "^^" :: h4 :: t =>
                           h1 :: "^^" :: h2 :: ">33" :: h3 :: "^^" :: h4 :: set_compare_gt t
(* 35 *)
| h1 :: "^^" :: h2 :: ">" :: h3 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: ">35" :: h3 :: "[":: m :: "]" :: set_compare_gt t
(* 3 *)
| h1 :: "^^" :: h2 :: ">" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: ">30" :: "$" :: h3 :: set_compare_gt t
                          | LOCAL  => h1 :: "^^" :: h2 :: ">31" :: h3 :: set_compare_gt t
                          | VAR    => h1 :: "^^" :: h2 :: ">32" :: h3 :: set_compare_gt t
                          | FUNf    => h1 :: "^^" :: h2 :: ">36" :: h3 :: set_compare_gt t
                          | _ => h1 :: "^^" :: h2 :: ">" :: h3 :: set_compare_gt t
                          end else h1 :: "^^" :: h2 :: ">" :: h3 :: set_compare_gt t
(* 54 *)
| h1 :: "[" :: n :: "]" :: ">" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "[" :: n :: "]" :: ">54" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: set_compare_gt t
(* 53 *)
| h1 :: "[":: n :: "]" :: ">" :: h2 :: "^^" :: h3 :: t =>
                          h1 :: "[":: n :: "]" :: ">53" :: h2 :: "^^" :: h3 :: set_compare_gt t
(* 55 *)
| h1 :: "[":: n :: "]" :: ">" :: h2 :: "[":: m :: "]" :: t =>
                    h1 :: "[":: n :: "]" :: ">55" :: h2 :: "[":: m :: "]" :: set_compare_gt t
(* 2 *)
| h1 :: "[" :: n :: "]" :: ">" :: h2 :: t => if ( if_who (who h1) VAR ) then
                          match who h2 with
                          | NUMBER => h1 :: "[" :: n :: "]" :: ">50" :: "$" :: h2 :: set_compare_gt t
                          | LOCAL  => h1 :: "[" :: n :: "]" :: ">51" :: h2 :: set_compare_gt t
                          | VAR    => h1 :: "[" :: n :: "]" :: ">52" :: h2 :: set_compare_gt t
                          | FUNf    => h1 :: "[" :: n :: "]" :: ">56" :: h2 :: set_compare_gt t
                          | _ => h1 :: "[" :: n :: "]" :: ">" :: h2 :: set_compare_gt t
                          end else h1 :: "[" :: n :: "]" :: ">" :: h2 :: set_compare_gt t
(* 6 *)
| h1 :: ">" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: ">04" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_gt t
                          | LOCAL  => h1 :: ">14" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_gt t
                          | VAR    => h1 :: ">24" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_gt t
                          | FUNf    => h1 :: ">64" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_gt t
                          | _ => h1 :: ">" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_gt t
                          end
(* 5 *)
| h1 :: ">" :: h2 :: "^^" :: h3 :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: ">03" :: h2 :: "^^" :: h3 :: set_compare_gt t
                          | LOCAL  => h1 :: ">13" :: h2 :: "^^" :: h3 :: set_compare_gt t
                          | VAR    => h1 :: ">23" :: h2 :: "^^" :: h3 :: set_compare_gt t
                          | FUNf    => h1 :: ">63" :: h2 :: "^^" :: h3 :: set_compare_gt t
                          | _ => h1 :: ">" :: h2 :: "^^" :: h3 :: set_compare_gt t
                          end
(* 7 *)
| h1 :: ">" :: h2 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: ">05" :: h2 :: "[":: n :: "]" :: set_compare_gt t
                          | LOCAL  => h1 :: ">15" :: h2 :: "[":: n :: "]" :: set_compare_gt t
                          | VAR    => h1 :: ">25" :: h2 :: "[":: n :: "]" :: set_compare_gt t
                          | FUNf    => h1 :: ">65" :: h2 :: "[":: n :: "]" :: set_compare_gt t
                          | _ => h1 :: ">" :: h2 :: "[":: n :: "]" :: set_compare_gt t
                          end
(* 1 *)
| h1 :: ">" :: h2 :: t => match who h1, who h2 with
                          | NUMBER, NUMBER => "$" :: h1 :: ">00" :: "$" :: h2 :: set_compare_gt t
                          | NUMBER, LOCAL  => "$" :: h1 :: ">01" :: h2 :: set_compare_gt t
                          | NUMBER, VAR    => "$" :: h1 :: ">02" :: h2 :: set_compare_gt t
                          | NUMBER, FUNf   => "$" :: h1 :: ">06" :: h2 :: set_compare_gt t
                          | LOCAL, NUMBER => h1 :: ">10" :: "$" :: h2 :: set_compare_gt t
                          | LOCAL, LOCAL  => h1 :: ">11" :: h2 :: set_compare_gt t
                          | LOCAL, VAR    => h1 :: ">12" :: h2 :: set_compare_gt t
                          | LOCAL, FUNf   => h1 :: ">16" :: h2 :: set_compare_gt t
                          | VAR,   NUMBER => h1 :: ">20" :: "$" :: h2 :: set_compare_gt t   
                          | VAR,   LOCAL  => h1 :: ">21" :: h2 :: set_compare_gt t
                          | VAR,   VAR    => h1 :: ">22" :: h2 :: set_compare_gt t
                          | VAR,   FUNf   => h1 :: ">26" :: h2 :: set_compare_gt t
                          | FUNf,  NUMBER => h1 :: ">60" :: "$" :: h2 :: set_compare_gt t   
                          | FUNf,   LOCAL  => h1 :: ">61" :: h2 :: set_compare_gt t
                          | FUNf,   VAR    => h1 :: ">62" :: h2 :: set_compare_gt t
                          | FUNf,   FUNf   => h1 :: ">66" :: h2 :: set_compare_gt t
                          | _, _ => h1 :: ">" :: h2 :: set_compare_gt t
                          end
| h :: t => h :: set_compare_gt t
end.

Fixpoint set_compare_eq(sl:list string) :=
match sl with
| nil => nil
(* 44 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"==" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "[":: n :: "]" ::"==44" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_compare_eq t
(* 43 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"==" :: h3 :: "^^" :: h4 :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"==43" :: h3 :: "^^" :: h4 :: set_compare_eq t
(* 45 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"==" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"==45" :: h3 :: "[":: m :: "]" :: set_compare_eq t
(* 4 *)
| h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "==" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "==40" :: "$" :: h3 :: set_compare_eq t
                          | LOCAL  => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "==41" :: h3 :: set_compare_eq t
                          | VAR    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "==42" :: h3 :: set_compare_eq t
                          | FUNf    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "==46" :: h3 :: set_compare_eq t
                          | _ => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "==" :: h3 :: set_compare_eq t
                          end else h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "==" :: h3 :: set_compare_eq t

(* 34 *)
| h1 :: "^^" :: h2 :: "==" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "==34" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_compare_eq t
(* 33 *)
| h1 :: "^^" :: h2 :: "==" :: h3 :: "^^" :: h4 :: t =>
                           h1 :: "^^" :: h2 :: "==33" :: h3 :: "^^" :: h4 :: set_compare_eq t
(* 35 *)
| h1 :: "^^" :: h2 :: "==" :: h3 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "==35" :: h3 :: "[":: m :: "]" :: set_compare_eq t
(* 3 *)
| h1 :: "^^" :: h2 :: "==" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "==30" :: "$" :: h3 :: set_compare_eq t
                          | LOCAL  => h1 :: "^^" :: h2 :: "==31" :: h3 :: set_compare_eq t
                          | VAR    => h1 :: "^^" :: h2 :: "==32" :: h3 :: set_compare_eq t
                          | FUNf    => h1 :: "^^" :: h2 :: "==36" :: h3 :: set_compare_eq t
                          | _ => h1 :: "^^" :: h2 :: "==" :: h3 :: set_compare_eq t
                          end else h1 :: "^^" :: h2 :: "==" :: h3 :: set_compare_eq t
(* 54 *)
| h1 :: "[" :: n :: "]" :: "==" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "[" :: n :: "]" :: "==54" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: set_compare_eq t
(* 53 *)
| h1 :: "[":: n :: "]" :: "==" :: h2 :: "^^" :: h3 :: t =>
                          h1 :: "[":: n :: "]" :: "==53" :: h2 :: "^^" :: h3 :: set_compare_eq t
(* 55 *)
| h1 :: "[":: n :: "]" :: "==" :: h2 :: "[":: m :: "]" :: t =>
                    h1 :: "[":: n :: "]" :: "==55" :: h2 :: "[":: m :: "]" :: set_compare_eq t
(* 2 *)
| h1 :: "[" :: n :: "]" :: "==" :: h2 :: t => if ( if_who (who h1) VAR ) then
                          match who h2 with
                          | NUMBER => h1 :: "[" :: n :: "]" :: "==50" :: "$" :: h2 :: set_compare_eq t
                          | LOCAL  => h1 :: "[" :: n :: "]" :: "==51" :: h2 :: set_compare_eq t
                          | VAR    => h1 :: "[" :: n :: "]" :: "==52" :: h2 :: set_compare_eq t
                          | FUNf    => h1 :: "[" :: n :: "]" :: "==56" :: h2 :: set_compare_eq t
                          | _ => h1 :: "[" :: n :: "]" :: "==" :: h2 :: set_compare_eq t
                          end else h1 :: "[" :: n :: "]" :: "==" :: h2 :: set_compare_eq t
(* 6 *)
| h1 :: "==" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "==04" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_eq t
                          | LOCAL  => h1 :: "==14" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_eq t
                          | VAR    => h1 :: "==24" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_eq t
                          | FUNf    => h1 :: "==64" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_eq t
                          | _ => h1 :: "==" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_eq t
                          end
(* 5 *)
| h1 :: "==" :: h2 :: "^^" :: h3 :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "==03" :: h2 :: "^^" :: h3 :: set_compare_eq t
                          | LOCAL  => h1 :: "==13" :: h2 :: "^^" :: h3 :: set_compare_eq t
                          | VAR    => h1 :: "==23" :: h2 :: "^^" :: h3 :: set_compare_eq t
                          | FUNf    => h1 :: "==63" :: h2 :: "^^" :: h3 :: set_compare_eq t
                          | _ => h1 :: "==" :: h2 :: "^^" :: h3 :: set_compare_eq t
                          end
(* 7 *)
| h1 :: "==" :: h2 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "==05" :: h2 :: "[":: n :: "]" :: set_compare_eq t
                          | LOCAL  => h1 :: "==15" :: h2 :: "[":: n :: "]" :: set_compare_eq t
                          | VAR    => h1 :: "==25" :: h2 :: "[":: n :: "]" :: set_compare_eq t
                          | FUNf    => h1 :: "==65" :: h2 :: "[":: n :: "]" :: set_compare_eq t
                          | _ => h1 :: "==" :: h2 :: "[":: n :: "]" :: set_compare_eq t
                          end
(* 1 *)
| h1 :: "==" :: h2 :: t => match who h1, who h2 with
                          | NUMBER, NUMBER => "$" :: h1 :: "==00" :: "$" :: h2 :: set_compare_eq t
                          | NUMBER, LOCAL  => "$" :: h1 :: "==01" :: h2 :: set_compare_eq t
                          | NUMBER, VAR    => "$" :: h1 :: "==02" :: h2 :: set_compare_eq t
                          | NUMBER, FUNf   => "$" :: h1 :: "==06" :: h2 :: set_compare_eq t
                          | LOCAL, NUMBER => h1 :: "==10" :: "$" :: h2 :: set_compare_eq t
                          | LOCAL, LOCAL  => h1 :: "==11" :: h2 :: set_compare_eq t
                          | LOCAL, VAR    => h1 :: "==12" :: h2 :: set_compare_eq t
                          | LOCAL, FUNf   => h1 :: "==16" :: h2 :: set_compare_eq t
                          | VAR,   NUMBER => h1 :: "==20" :: "$" :: h2 :: set_compare_eq t   
                          | VAR,   LOCAL  => h1 :: "==21" :: h2 :: set_compare_eq t
                          | VAR,   VAR    => h1 :: "==22" :: h2 :: set_compare_eq t
                          | VAR,   FUNf   => h1 :: "==26" :: h2 :: set_compare_eq t
                          | FUNf,  NUMBER => h1 :: "==60" :: "$" :: h2 :: set_compare_eq t   
                          | FUNf,   LOCAL  => h1 :: "==61" :: h2 :: set_compare_eq t
                          | FUNf,   VAR    => h1 :: "==62" :: h2 :: set_compare_eq t
                          | FUNf,   FUNf   => h1 :: "==66" :: h2 :: set_compare_eq t
                          | _, _ => h1 :: "==" :: h2 :: set_compare_eq t
                          end
| h :: t => h :: set_compare_eq t
end.

Fixpoint set_compare_ne(sl:list string) :=
match sl with
| nil => nil
(* 44 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"!=" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "[":: n :: "]" ::"!=44" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_compare_ne t
(* 43 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"!=" :: h3 :: "^^" :: h4 :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"!=43" :: h3 :: "^^" :: h4 :: set_compare_ne t
(* 45 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"!=" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"!=45" :: h3 :: "[":: m :: "]" :: set_compare_ne t
(* 4 *)
| h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "!=" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "!=40" :: "$" :: h3 :: set_compare_ne t
                          | LOCAL  => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "!=41" :: h3 :: set_compare_ne t
                          | VAR    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "!=42" :: h3 :: set_compare_ne t
                          | FUNf    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "!=46" :: h3 :: set_compare_ne t
                          | _ => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "!=" :: h3 :: set_compare_ne t
                          end else h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "!=" :: h3 :: set_compare_ne t

(* 34 *)
| h1 :: "^^" :: h2 :: "!=" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "!=34" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_compare_ne t
(* 33 *)
| h1 :: "^^" :: h2 :: "!=" :: h3 :: "^^" :: h4 :: t =>
                           h1 :: "^^" :: h2 :: "!=33" :: h3 :: "^^" :: h4 :: set_compare_ne t
(* 35 *)
| h1 :: "^^" :: h2 :: "!=" :: h3 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "!=35" :: h3 :: "[":: m :: "]" :: set_compare_ne t
(* 3 *)
| h1 :: "^^" :: h2 :: "!=" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "!=30" :: "$" :: h3 :: set_compare_ne t
                          | LOCAL  => h1 :: "^^" :: h2 :: "!=31" :: h3 :: set_compare_ne t
                          | VAR    => h1 :: "^^" :: h2 :: "!=32" :: h3 :: set_compare_ne t
                          | FUNf    => h1 :: "^^" :: h2 :: "!=36" :: h3 :: set_compare_ne t
                          | _ => h1 :: "^^" :: h2 :: "!=" :: h3 :: set_compare_ne t
                          end else h1 :: "^^" :: h2 :: "!=" :: h3 :: set_compare_ne t
(* 54 *)
| h1 :: "[" :: n :: "]" :: "!=" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "[" :: n :: "]" :: "!=54" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: set_compare_ne t
(* 53 *)
| h1 :: "[":: n :: "]" :: "!=" :: h2 :: "^^" :: h3 :: t =>
                          h1 :: "[":: n :: "]" :: "!=53" :: h2 :: "^^" :: h3 :: set_compare_ne t
(* 55 *)
| h1 :: "[":: n :: "]" :: "!=" :: h2 :: "[":: m :: "]" :: t =>
                    h1 :: "[":: n :: "]" :: "!=55" :: h2 :: "[":: m :: "]" :: set_compare_ne t
(* 2 *)
| h1 :: "[" :: n :: "]" :: "!=" :: h2 :: t => if ( if_who (who h1) VAR ) then
                          match who h2 with
                          | NUMBER => h1 :: "[" :: n :: "]" :: "!=50" :: "$" :: h2 :: set_compare_ne t
                          | LOCAL  => h1 :: "[" :: n :: "]" :: "!=51" :: h2 :: set_compare_ne t
                          | VAR    => h1 :: "[" :: n :: "]" :: "!=52" :: h2 :: set_compare_ne t
                          | FUNf    => h1 :: "[" :: n :: "]" :: "!=56" :: h2 :: set_compare_ne t
                          | _ => h1 :: "[" :: n :: "]" :: "!=" :: h2 :: set_compare_ne t
                          end else h1 :: "[" :: n :: "]" :: "!=" :: h2 :: set_compare_ne t
(* 6 *)
| h1 :: "!=" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "!=04" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_ne t
                          | LOCAL  => h1 :: "!=14" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_ne t
                          | VAR    => h1 :: "!=24" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_ne t
                          | FUNf    => h1 :: "!=64" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_ne t
                          | _ => h1 :: "!=" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_compare_ne t
                          end
(* 5 *)
| h1 :: "!=" :: h2 :: "^^" :: h3 :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "!=03" :: h2 :: "^^" :: h3 :: set_compare_ne t
                          | LOCAL  => h1 :: "!=13" :: h2 :: "^^" :: h3 :: set_compare_ne t
                          | VAR    => h1 :: "!=23" :: h2 :: "^^" :: h3 :: set_compare_ne t
                          | FUNf    => h1 :: "!=63" :: h2 :: "^^" :: h3 :: set_compare_ne t
                          | _ => h1 :: "!=" :: h2 :: "^^" :: h3 :: set_compare_ne t
                          end
(* 7 *)
| h1 :: "!=" :: h2 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "!=05" :: h2 :: "[":: n :: "]" :: set_compare_ne t
                          | LOCAL  => h1 :: "!=15" :: h2 :: "[":: n :: "]" :: set_compare_ne t
                          | VAR    => h1 :: "!=25" :: h2 :: "[":: n :: "]" :: set_compare_ne t
                          | FUNf    => h1 :: "!=65" :: h2 :: "[":: n :: "]" :: set_compare_ne t
                          | _ => h1 :: "!=" :: h2 :: "[":: n :: "]" :: set_compare_ne t
                          end
(* 1 *)
| h1 :: "!=" :: h2 :: t => match who h1, who h2 with
                          | NUMBER, NUMBER => "$" :: h1 :: "!=00" :: "$" :: h2 :: set_compare_ne t
                          | NUMBER, LOCAL  => "$" :: h1 :: "!=01" :: h2 :: set_compare_ne t
                          | NUMBER, VAR    => "$" :: h1 :: "!=02" :: h2 :: set_compare_ne t
                          | NUMBER, FUNf   => "$" :: h1 :: "!=06" :: h2 :: set_compare_ne t
                          | LOCAL, NUMBER => h1 :: "!=10" :: "$" :: h2 :: set_compare_ne t
                          | LOCAL, LOCAL  => h1 :: "!=11" :: h2 :: set_compare_ne t
                          | LOCAL, VAR    => h1 :: "!=12" :: h2 :: set_compare_ne t
                          | LOCAL, FUNf   => h1 :: "!=16" :: h2 :: set_compare_ne t
                          | VAR,   NUMBER => h1 :: "!=20" :: "$" :: h2 :: set_compare_ne t   
                          | VAR,   LOCAL  => h1 :: "!=21" :: h2 :: set_compare_ne t
                          | VAR,   VAR    => h1 :: "!=22" :: h2 :: set_compare_ne t
                          | VAR,   FUNf   => h1 :: "!=26" :: h2 :: set_compare_ne t
                          | FUNf,  NUMBER => h1 :: "!=60" :: "$" :: h2 :: set_compare_ne t   
                          | FUNf,   LOCAL  => h1 :: "!=61" :: h2 :: set_compare_ne t
                          | FUNf,   VAR    => h1 :: "!=62" :: h2 :: set_compare_ne t
                          | FUNf,   FUNf   => h1 :: "!=66" :: h2 :: set_compare_ne t
                          | _, _ => h1 :: "!=" :: h2 :: set_compare_ne t
                          end
| h :: t => h :: set_compare_ne t
end.


Fixpoint set_assingment(sl:list string) :=
match sl with
| nil => nil
(* 44 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"=" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "[":: n :: "]" ::"=44" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_assingment t
(* 43 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"=" :: h3 :: "^^" :: h4 :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"=43" :: h3 :: "^^" :: h4 :: set_assingment t
(* 45 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"=" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"=45" :: h3 :: "[":: m :: "]" :: set_assingment t
(* 4 *)
| h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "=" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "=40" :: "$" :: h3 :: set_assingment t
                          | LOCAL  => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "=41" :: h3 :: set_assingment t
                          | VAR    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "=42" :: h3 :: set_assingment t
                          | FUNf    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "=46" :: h3 :: set_assingment t
                          | _ => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "=" :: h3 :: set_assingment t
                          end else h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "=" :: h3 :: set_assingment t

(* 34 *)
| h1 :: "^^" :: h2 :: "=" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "=34" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_assingment t
(* 33 *)
| h1 :: "^^" :: h2 :: "=" :: h3 :: "^^" :: h4 :: t =>
                           h1 :: "^^" :: h2 :: "=33" :: h3 :: "^^" :: h4 :: set_assingment t
(* 35 *)
| h1 :: "^^" :: h2 :: "=" :: h3 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "=35" :: h3 :: "[":: m :: "]" :: set_assingment t
(* 3 *)
| h1 :: "^^" :: h2 :: "=" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "=30" :: "$" :: h3 :: set_assingment t
                          | LOCAL  => h1 :: "^^" :: h2 :: "=31" :: h3 :: set_assingment t
                          | VAR    => h1 :: "^^" :: h2 :: "=32" :: h3 :: set_assingment t
                          | FUNf    => h1 :: "^^" :: h2 :: "=36" :: h3 :: set_assingment t
                          | _ => h1 :: "^^" :: h2 :: "=" :: h3 :: set_assingment t
                          end else h1 :: "^^" :: h2 :: "=" :: h3 :: set_assingment t
(* 54 *)
| h1 :: "[" :: n :: "]" :: "=" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "[" :: n :: "]" :: "=54" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: set_assingment t
(* 53 *)
| h1 :: "[":: n :: "]" :: "=" :: h2 :: "^^" :: h3 :: t =>
                          h1 :: "[":: n :: "]" :: "=53" :: h2 :: "^^" :: h3 :: set_assingment t
(* 55 *)
| h1 :: "[":: n :: "]" :: "=" :: h2 :: "[":: m :: "]" :: t =>
                    h1 :: "[":: n :: "]" :: "=55" :: h2 :: "[":: m :: "]" :: set_assingment t
(* 2 *)
| h1 :: "[" :: n :: "]" :: "=" :: h2 :: t => if ( if_who (who h1) VAR ) then
                          match who h2 with
                          | NUMBER => h1 :: "[" :: n :: "]" :: "=50" :: "$" :: h2 :: set_assingment t
                          | LOCAL  => h1 :: "[" :: n :: "]" :: "=51" :: h2 :: set_assingment t
                          | VAR    => h1 :: "[" :: n :: "]" :: "=52" :: h2 :: set_assingment t
                          | FUNf    => h1 :: "[" :: n :: "]" :: "=56" :: h2 :: set_assingment t
                          | _ => h1 :: "[" :: n :: "]" :: "=" :: h2 :: set_assingment t
                          end else h1 :: "[" :: n :: "]" :: "=" :: h2 :: set_assingment t
(* 6 *)
| h1 :: "=" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "=04" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_assingment t
                          | LOCAL  => h1 :: "=14" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_assingment t
                          | VAR    => h1 :: "=24" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_assingment t
                          | FUNf    => h1 :: "=64" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_assingment t
                          | _ => h1 :: "=" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_assingment t
                          end
(* 5 *)
| h1 :: "=" :: h2 :: "^^" :: h3 :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "=03" :: h2 :: "^^" :: h3 :: set_assingment t
                          | LOCAL  => h1 :: "=13" :: h2 :: "^^" :: h3 :: set_assingment t
                          | VAR    => h1 :: "=23" :: h2 :: "^^" :: h3 :: set_assingment t
                          | FUNf    => h1 :: "=63" :: h2 :: "^^" :: h3 :: set_assingment t
                          | _ => h1 :: "=" :: h2 :: "^^" :: h3 :: set_assingment t
                          end
(* 7 *)
| h1 :: "=" :: h2 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "=05" :: h2 :: "[":: n :: "]" :: set_assingment t
                          | LOCAL  => h1 :: "=15" :: h2 :: "[":: n :: "]" :: set_assingment t
                          | VAR    => h1 :: "=25" :: h2 :: "[":: n :: "]" :: set_assingment t
                          | FUNf    => h1 :: "=65" :: h2 :: "[":: n :: "]" :: set_assingment t
                          | _ => h1 :: "=" :: h2 :: "[":: n :: "]" :: set_assingment t
                          end
(* 1 *)
| h1 :: "=" :: h2 :: t => match who h1, who h2 with
                          | NUMBER, NUMBER => "$" :: h1 :: "=00" :: "$" :: h2 :: set_assingment t
                          | NUMBER, LOCAL  => "$" :: h1 :: "=01" :: h2 :: set_assingment t
                          | NUMBER, VAR    => "$" :: h1 :: "=02" :: h2 :: set_assingment t
                          | NUMBER, FUNf   => "$" :: h1 :: "=06" :: h2 :: set_assingment t
                          | LOCAL, NUMBER => h1 :: "=10" :: "$" :: h2 :: set_assingment t
                          | LOCAL, LOCAL  => h1 :: "=11" :: h2 :: set_assingment t
                          | LOCAL, VAR    => h1 :: "=12" :: h2 :: set_assingment t
                          | LOCAL, FUNf   => h1 :: "=16" :: h2 :: set_assingment t
                          | VAR,   NUMBER => h1 :: "=20" :: "$" :: h2 :: set_assingment t   
                          | VAR,   LOCAL  => h1 :: "=21" :: h2 :: set_assingment t
                          | VAR,   VAR    => h1 :: "=22" :: h2 :: set_assingment t
                          | VAR,   FUNf   => h1 :: "=26" :: h2 :: set_assingment t
                          | FUNf,  NUMBER => h1 :: "=60" :: "$" :: h2 :: set_assingment t   
                          | FUNf,   LOCAL  => h1 :: "=61" :: h2 :: set_assingment t
                          | FUNf,   VAR    => h1 :: "=62" :: h2 :: set_assingment t
                          | FUNf,   FUNf   => h1 :: "=66" :: h2 :: set_assingment t
                          | _, _ => h1 :: "=" :: h2 :: set_assingment t
                          end
| h :: t => h :: set_assingment t
end.

Fixpoint set_plus_assingment(sl:list string) :=
match sl with
| nil => nil
(* 44 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"+=" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "[":: n :: "]" ::"+=44" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_plus_assingment t
(* 43 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"+=" :: h3 :: "^^" :: h4 :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"+=43" :: h3 :: "^^" :: h4 :: set_plus_assingment t
(* 45 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"+=" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"+=45" :: h3 :: "[":: m :: "]" :: set_plus_assingment t
(* 4 *)
| h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "+=" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "+=40" :: "$" :: h3 :: set_plus_assingment t
                          | LOCAL  => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "+=41" :: h3 :: set_plus_assingment t
                          | VAR    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "+=42" :: h3 :: set_plus_assingment t
                          | FUNf    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "+=46" :: h3 :: set_plus_assingment t
                          | _ => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "+=" :: h3 :: set_plus_assingment t
                          end else h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "+=" :: h3 :: set_plus_assingment t

(* 34 *)
| h1 :: "^^" :: h2 :: "+=" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "+=34" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_plus_assingment t
(* 33 *)
| h1 :: "^^" :: h2 :: "+=" :: h3 :: "^^" :: h4 :: t =>
                           h1 :: "^^" :: h2 :: "+=33" :: h3 :: "^^" :: h4 :: set_plus_assingment t
(* 35 *)
| h1 :: "^^" :: h2 :: "+=" :: h3 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "+=35" :: h3 :: "[":: m :: "]" :: set_plus_assingment t
(* 3 *)
| h1 :: "^^" :: h2 :: "+=" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "+=30" :: "$" :: h3 :: set_plus_assingment t
                          | LOCAL  => h1 :: "^^" :: h2 :: "+=31" :: h3 :: set_plus_assingment t
                          | VAR    => h1 :: "^^" :: h2 :: "+=32" :: h3 :: set_plus_assingment t
                          | FUNf    => h1 :: "^^" :: h2 :: "+=36" :: h3 :: set_plus_assingment t
                          | _ => h1 :: "^^" :: h2 :: "+=" :: h3 :: set_plus_assingment t
                          end else h1 :: "^^" :: h2 :: "+=" :: h3 :: set_plus_assingment t
(* 54 *)
| h1 :: "[" :: n :: "]" :: "+=" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "[" :: n :: "]" :: "+=54" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: set_plus_assingment t
(* 53 *)
| h1 :: "[":: n :: "]" :: "+=" :: h2 :: "^^" :: h3 :: t =>
                          h1 :: "[":: n :: "]" :: "+=53" :: h2 :: "^^" :: h3 :: set_plus_assingment t
(* 55 *)
| h1 :: "[":: n :: "]" :: "+=" :: h2 :: "[":: m :: "]" :: t =>
                    h1 :: "[":: n :: "]" :: "+=55" :: h2 :: "[":: m :: "]" :: set_plus_assingment t
(* 2 *)
| h1 :: "[" :: n :: "]" :: "+=" :: h2 :: t => if ( if_who (who h1) VAR ) then
                          match who h2 with
                          | NUMBER => h1 :: "[" :: n :: "]" :: "+=50" :: "$" :: h2 :: set_plus_assingment t
                          | LOCAL  => h1 :: "[" :: n :: "]" :: "+=51" :: h2 :: set_plus_assingment t
                          | VAR    => h1 :: "[" :: n :: "]" :: "+=52" :: h2 :: set_plus_assingment t
                          | FUNf    => h1 :: "[" :: n :: "]" :: "+=56" :: h2 :: set_plus_assingment t
                          | _ => h1 :: "[" :: n :: "]" :: "+=" :: h2 :: set_plus_assingment t
                          end else h1 :: "[" :: n :: "]" :: "+=" :: h2 :: set_plus_assingment t
(* 6 *)
| h1 :: "+=" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "+=04" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_plus_assingment t
                          | LOCAL  => h1 :: "+=14" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_plus_assingment t
                          | VAR    => h1 :: "+=24" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_plus_assingment t
                          | FUNf    => h1 :: "+=64" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_plus_assingment t
                          | _ => h1 :: "+=" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_plus_assingment t
                          end
(* 5 *)
| h1 :: "+=" :: h2 :: "^^" :: h3 :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "+=03" :: h2 :: "^^" :: h3 :: set_plus_assingment t
                          | LOCAL  => h1 :: "+=13" :: h2 :: "^^" :: h3 :: set_plus_assingment t
                          | VAR    => h1 :: "+=23" :: h2 :: "^^" :: h3 :: set_plus_assingment t
                          | FUNf    => h1 :: "+=63" :: h2 :: "^^" :: h3 :: set_plus_assingment t
                          | _ => h1 :: "+=" :: h2 :: "^^" :: h3 :: set_plus_assingment t
                          end
(* 7 *)
| h1 :: "+=" :: h2 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "+=05" :: h2 :: "[":: n :: "]" :: set_plus_assingment t
                          | LOCAL  => h1 :: "+=15" :: h2 :: "[":: n :: "]" :: set_plus_assingment t
                          | VAR    => h1 :: "+=25" :: h2 :: "[":: n :: "]" :: set_plus_assingment t
                          | FUNf    => h1 :: "+=65" :: h2 :: "[":: n :: "]" :: set_plus_assingment t
                          | _ => h1 :: "+=" :: h2 :: "[":: n :: "]" :: set_plus_assingment t
                          end
(* 1 *)
| h1 :: "+=" :: h2 :: t => match who h1, who h2 with
                          | NUMBER, NUMBER => "$" :: h1 :: "+=00" :: "$" :: h2 :: set_plus_assingment t
                          | NUMBER, LOCAL  => "$" :: h1 :: "+=01" :: h2 :: set_plus_assingment t
                          | NUMBER, VAR    => "$" :: h1 :: "+=02" :: h2 :: set_plus_assingment t
                          | NUMBER, FUNf   => "$" :: h1 :: "+=06" :: h2 :: set_plus_assingment t
                          | LOCAL, NUMBER => h1 :: "+=10" :: "$" :: h2 :: set_plus_assingment t
                          | LOCAL, LOCAL  => h1 :: "+=11" :: h2 :: set_plus_assingment t
                          | LOCAL, VAR    => h1 :: "+=12" :: h2 :: set_plus_assingment t
                          | LOCAL, FUNf   => h1 :: "+=16" :: h2 :: set_plus_assingment t
                          | VAR,   NUMBER => h1 :: "+=20" :: "$" :: h2 :: set_plus_assingment t   
                          | VAR,   LOCAL  => h1 :: "+=21" :: h2 :: set_plus_assingment t
                          | VAR,   VAR    => h1 :: "+=22" :: h2 :: set_plus_assingment t
                          | VAR,   FUNf   => h1 :: "+=26" :: h2 :: set_plus_assingment t
                          | FUNf,  NUMBER => h1 :: "+=60" :: "$" :: h2 :: set_plus_assingment t   
                          | FUNf,   LOCAL  => h1 :: "+=61" :: h2 :: set_plus_assingment t
                          | FUNf,   VAR    => h1 :: "+=62" :: h2 :: set_plus_assingment t
                          | FUNf,   FUNf   => h1 :: "+=66" :: h2 :: set_plus_assingment t
                          | _, _ => h1 :: "+=" :: h2 :: set_plus_assingment t
                          end
| h :: t => h :: set_plus_assingment t
end.

Fixpoint set_minus_assingment(sl:list string) :=
match sl with
| nil => nil
(* 44 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"-=" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "[":: n :: "]" ::"-=44" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_minus_assingment t
(* 43 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"-=" :: h3 :: "^^" :: h4 :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"-=43" :: h3 :: "^^" :: h4 :: set_minus_assingment t
(* 45 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"-=" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"-=45" :: h3 :: "[":: m :: "]" :: set_minus_assingment t
(* 4 *)
| h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "-=" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "-=40" :: "$" :: h3 :: set_minus_assingment t
                          | LOCAL  => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "-=41" :: h3 :: set_minus_assingment t
                          | VAR    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "-=42" :: h3 :: set_minus_assingment t
                          | FUNf    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "-=46" :: h3 :: set_minus_assingment t
                          | _ => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "-=" :: h3 :: set_minus_assingment t
                          end else h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "-=" :: h3 :: set_minus_assingment t

(* 34 *)
| h1 :: "^^" :: h2 :: "-=" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "-=34" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_minus_assingment t
(* 33 *)
| h1 :: "^^" :: h2 :: "-=" :: h3 :: "^^" :: h4 :: t =>
                           h1 :: "^^" :: h2 :: "-=33" :: h3 :: "^^" :: h4 :: set_minus_assingment t
(* 35 *)
| h1 :: "^^" :: h2 :: "-=" :: h3 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "-=35" :: h3 :: "[":: m :: "]" :: set_minus_assingment t
(* 3 *)
| h1 :: "^^" :: h2 :: "-=" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "-=30" :: "$" :: h3 :: set_minus_assingment t
                          | LOCAL  => h1 :: "^^" :: h2 :: "-=31" :: h3 :: set_minus_assingment t
                          | VAR    => h1 :: "^^" :: h2 :: "-=32" :: h3 :: set_minus_assingment t
                          | FUNf    => h1 :: "^^" :: h2 :: "-=36" :: h3 :: set_minus_assingment t
                          | _ => h1 :: "^^" :: h2 :: "-=" :: h3 :: set_minus_assingment t
                          end else h1 :: "^^" :: h2 :: "-=" :: h3 :: set_minus_assingment t
(* 54 *)
| h1 :: "[" :: n :: "]" :: "-=" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "[" :: n :: "]" :: "-=54" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: set_minus_assingment t
(* 53 *)
| h1 :: "[":: n :: "]" :: "-=" :: h2 :: "^^" :: h3 :: t =>
                          h1 :: "[":: n :: "]" :: "-=53" :: h2 :: "^^" :: h3 :: set_minus_assingment t
(* 55 *)
| h1 :: "[":: n :: "]" :: "-=" :: h2 :: "[":: m :: "]" :: t =>
                    h1 :: "[":: n :: "]" :: "-=55" :: h2 :: "[":: m :: "]" :: set_minus_assingment t
(* 2 *)
| h1 :: "[" :: n :: "]" :: "-=" :: h2 :: t => if ( if_who (who h1) VAR ) then
                          match who h2 with
                          | NUMBER => h1 :: "[" :: n :: "]" :: "-=50" :: "$" :: h2 :: set_minus_assingment t
                          | LOCAL  => h1 :: "[" :: n :: "]" :: "-=51" :: h2 :: set_minus_assingment t
                          | VAR    => h1 :: "[" :: n :: "]" :: "-=52" :: h2 :: set_minus_assingment t
                          | FUNf    => h1 :: "[" :: n :: "]" :: "-=56" :: h2 :: set_minus_assingment t
                          | _ => h1 :: "[" :: n :: "]" :: "-=" :: h2 :: set_minus_assingment t
                          end else h1 :: "[" :: n :: "]" :: "-=" :: h2 :: set_minus_assingment t
(* 6 *)
| h1 :: "-=" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "-=04" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_minus_assingment t
                          | LOCAL  => h1 :: "-=14" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_minus_assingment t
                          | VAR    => h1 :: "-=24" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_minus_assingment t
                          | FUNf    => h1 :: "-=64" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_minus_assingment t
                          | _ => h1 :: "-=" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_minus_assingment t
                          end
(* 5 *)
| h1 :: "-=" :: h2 :: "^^" :: h3 :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "-=03" :: h2 :: "^^" :: h3 :: set_minus_assingment t
                          | LOCAL  => h1 :: "-=13" :: h2 :: "^^" :: h3 :: set_minus_assingment t
                          | VAR    => h1 :: "-=23" :: h2 :: "^^" :: h3 :: set_minus_assingment t
                          | FUNf    => h1 :: "-=63" :: h2 :: "^^" :: h3 :: set_minus_assingment t
                          | _ => h1 :: "-=" :: h2 :: "^^" :: h3 :: set_minus_assingment t
                          end
(* 7 *)
| h1 :: "-=" :: h2 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "-=05" :: h2 :: "[":: n :: "]" :: set_minus_assingment t
                          | LOCAL  => h1 :: "-=15" :: h2 :: "[":: n :: "]" :: set_minus_assingment t
                          | VAR    => h1 :: "-=25" :: h2 :: "[":: n :: "]" :: set_minus_assingment t
                          | FUNf    => h1 :: "-=65" :: h2 :: "[":: n :: "]" :: set_minus_assingment t
                          | _ => h1 :: "-=" :: h2 :: "[":: n :: "]" :: set_minus_assingment t
                          end
(* 1 *)
| h1 :: "-=" :: h2 :: t => match who h1, who h2 with
                          | NUMBER, NUMBER => "$" :: h1 :: "-=00" :: "$" :: h2 :: set_minus_assingment t
                          | NUMBER, LOCAL  => "$" :: h1 :: "-=01" :: h2 :: set_minus_assingment t
                          | NUMBER, VAR    => "$" :: h1 :: "-=02" :: h2 :: set_minus_assingment t
                          | NUMBER, FUNf   => "$" :: h1 :: "-=06" :: h2 :: set_minus_assingment t
                          | LOCAL, NUMBER => h1 :: "-=10" :: "$" :: h2 :: set_minus_assingment t
                          | LOCAL, LOCAL  => h1 :: "-=11" :: h2 :: set_minus_assingment t
                          | LOCAL, VAR    => h1 :: "-=12" :: h2 :: set_minus_assingment t
                          | LOCAL, FUNf   => h1 :: "-=16" :: h2 :: set_minus_assingment t
                          | VAR,   NUMBER => h1 :: "-=20" :: "$" :: h2 :: set_minus_assingment t   
                          | VAR,   LOCAL  => h1 :: "-=21" :: h2 :: set_minus_assingment t
                          | VAR,   VAR    => h1 :: "-=22" :: h2 :: set_minus_assingment t
                          | VAR,   FUNf   => h1 :: "-=26" :: h2 :: set_minus_assingment t
                          | FUNf,  NUMBER => h1 :: "-=60" :: "$" :: h2 :: set_minus_assingment t   
                          | FUNf,   LOCAL  => h1 :: "-=61" :: h2 :: set_minus_assingment t
                          | FUNf,   VAR    => h1 :: "-=62" :: h2 :: set_minus_assingment t
                          | FUNf,   FUNf   => h1 :: "-=66" :: h2 :: set_minus_assingment t
                          | _, _ => h1 :: "-=" :: h2 :: set_minus_assingment t
                          end
| h :: t => h :: set_minus_assingment t
end.

Fixpoint set_mult_assingment(sl:list string) :=
match sl with
| nil => nil
(* 44 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"*=" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "[":: n :: "]" ::"*=44" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_mult_assingment t
(* 43 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"*=" :: h3 :: "^^" :: h4 :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"*=43" :: h3 :: "^^" :: h4 :: set_mult_assingment t
(* 45 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"*=" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"*=45" :: h3 :: "[":: m :: "]" :: set_mult_assingment t
(* 4 *)
| h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "*=" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "*=40" :: "$" :: h3 :: set_mult_assingment t
                          | LOCAL  => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "*=41" :: h3 :: set_mult_assingment t
                          | VAR    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "*=42" :: h3 :: set_mult_assingment t
                          | FUNf    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "*=46" :: h3 :: set_mult_assingment t
                          | _ => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "*=" :: h3 :: set_mult_assingment t
                          end else h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "*=" :: h3 :: set_mult_assingment t

(* 34 *)
| h1 :: "^^" :: h2 :: "*=" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "*=34" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_mult_assingment t
(* 33 *)
| h1 :: "^^" :: h2 :: "*=" :: h3 :: "^^" :: h4 :: t =>
                           h1 :: "^^" :: h2 :: "*=33" :: h3 :: "^^" :: h4 :: set_mult_assingment t
(* 35 *)
| h1 :: "^^" :: h2 :: "*=" :: h3 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "*=35" :: h3 :: "[":: m :: "]" :: set_mult_assingment t
(* 3 *)
| h1 :: "^^" :: h2 :: "*=" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "*=30" :: "$" :: h3 :: set_mult_assingment t
                          | LOCAL  => h1 :: "^^" :: h2 :: "*=31" :: h3 :: set_mult_assingment t
                          | VAR    => h1 :: "^^" :: h2 :: "*=32" :: h3 :: set_mult_assingment t
                          | FUNf    => h1 :: "^^" :: h2 :: "*=36" :: h3 :: set_mult_assingment t
                          | _ => h1 :: "^^" :: h2 :: "*=" :: h3 :: set_mult_assingment t
                          end else h1 :: "^^" :: h2 :: "*=" :: h3 :: set_mult_assingment t
(* 54 *)
| h1 :: "[" :: n :: "]" :: "*=" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "[" :: n :: "]" :: "*=54" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: set_mult_assingment t
(* 53 *)
| h1 :: "[":: n :: "]" :: "*=" :: h2 :: "^^" :: h3 :: t =>
                          h1 :: "[":: n :: "]" :: "*=53" :: h2 :: "^^" :: h3 :: set_mult_assingment t
(* 55 *)
| h1 :: "[":: n :: "]" :: "*=" :: h2 :: "[":: m :: "]" :: t =>
                    h1 :: "[":: n :: "]" :: "*=55" :: h2 :: "[":: m :: "]" :: set_mult_assingment t
(* 2 *)
| h1 :: "[" :: n :: "]" :: "*=" :: h2 :: t => if ( if_who (who h1) VAR ) then
                          match who h2 with
                          | NUMBER => h1 :: "[" :: n :: "]" :: "*=50" :: "$" :: h2 :: set_mult_assingment t
                          | LOCAL  => h1 :: "[" :: n :: "]" :: "*=51" :: h2 :: set_mult_assingment t
                          | VAR    => h1 :: "[" :: n :: "]" :: "*=52" :: h2 :: set_mult_assingment t
                          | FUNf    => h1 :: "[" :: n :: "]" :: "*=56" :: h2 :: set_mult_assingment t
                          | _ => h1 :: "[" :: n :: "]" :: "*=" :: h2 :: set_mult_assingment t
                          end else h1 :: "[" :: n :: "]" :: "*=" :: h2 :: set_mult_assingment t
(* 6 *)
| h1 :: "*=" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "*=04" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_mult_assingment t
                          | LOCAL  => h1 :: "*=14" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_mult_assingment t
                          | VAR    => h1 :: "*=24" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_mult_assingment t
                          | FUNf    => h1 :: "*=64" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_mult_assingment t
                          | _ => h1 :: "*=" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_mult_assingment t
                          end
(* 5 *)
| h1 :: "*=" :: h2 :: "^^" :: h3 :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "*=03" :: h2 :: "^^" :: h3 :: set_mult_assingment t
                          | LOCAL  => h1 :: "*=13" :: h2 :: "^^" :: h3 :: set_mult_assingment t
                          | VAR    => h1 :: "*=23" :: h2 :: "^^" :: h3 :: set_mult_assingment t
                          | FUNf    => h1 :: "*=63" :: h2 :: "^^" :: h3 :: set_mult_assingment t
                          | _ => h1 :: "*=" :: h2 :: "^^" :: h3 :: set_mult_assingment t
                          end
(* 7 *)
| h1 :: "*=" :: h2 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "*=05" :: h2 :: "[":: n :: "]" :: set_mult_assingment t
                          | LOCAL  => h1 :: "*=15" :: h2 :: "[":: n :: "]" :: set_mult_assingment t
                          | VAR    => h1 :: "*=25" :: h2 :: "[":: n :: "]" :: set_mult_assingment t
                          | FUNf    => h1 :: "*=65" :: h2 :: "[":: n :: "]" :: set_mult_assingment t
                          | _ => h1 :: "*=" :: h2 :: "[":: n :: "]" :: set_mult_assingment t
                          end
(* 1 *)
| h1 :: "*=" :: h2 :: t => match who h1, who h2 with
                          | NUMBER, NUMBER => "$" :: h1 :: "*=00" :: "$" :: h2 :: set_mult_assingment t
                          | NUMBER, LOCAL  => "$" :: h1 :: "*=01" :: h2 :: set_mult_assingment t
                          | NUMBER, VAR    => "$" :: h1 :: "*=02" :: h2 :: set_mult_assingment t
                          | NUMBER, FUNf   => "$" :: h1 :: "*=06" :: h2 :: set_mult_assingment t
                          | LOCAL, NUMBER => h1 :: "*=10" :: "$" :: h2 :: set_mult_assingment t
                          | LOCAL, LOCAL  => h1 :: "*=11" :: h2 :: set_mult_assingment t
                          | LOCAL, VAR    => h1 :: "*=12" :: h2 :: set_mult_assingment t
                          | LOCAL, FUNf   => h1 :: "*=16" :: h2 :: set_mult_assingment t
                          | VAR,   NUMBER => h1 :: "*=20" :: "$" :: h2 :: set_mult_assingment t   
                          | VAR,   LOCAL  => h1 :: "*=21" :: h2 :: set_mult_assingment t
                          | VAR,   VAR    => h1 :: "*=22" :: h2 :: set_mult_assingment t
                          | VAR,   FUNf   => h1 :: "*=26" :: h2 :: set_mult_assingment t
                          | FUNf,  NUMBER => h1 :: "*=60" :: "$" :: h2 :: set_mult_assingment t   
                          | FUNf,   LOCAL  => h1 :: "*=61" :: h2 :: set_mult_assingment t
                          | FUNf,   VAR    => h1 :: "*=62" :: h2 :: set_mult_assingment t
                          | FUNf,   FUNf   => h1 :: "*=66" :: h2 :: set_mult_assingment t
                          | _, _ => h1 :: "*=" :: h2 :: set_mult_assingment t
                          end
| h :: t => h :: set_mult_assingment t
end.

Fixpoint set_div_assingment(sl:list string) :=
match sl with
| nil => nil
(* 44 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"/=" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "[":: n :: "]" ::"/=44" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_div_assingment t
(* 43 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"/=" :: h3 :: "^^" :: h4 :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"/=43" :: h3 :: "^^" :: h4 :: set_div_assingment t
(* 45 *)
| h1 :: "^^" :: h2 :: "[":: n :: "]" ::"/=" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "^^" :: h2 :: "[":: n :: "]" ::"/=45" :: h3 :: "[":: m :: "]" :: set_div_assingment t
(* 4 *)
| h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "/=" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "/=40" :: "$" :: h3 :: set_div_assingment t
                          | LOCAL  => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "/=41" :: h3 :: set_div_assingment t
                          | VAR    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "/=42" :: h3 :: set_div_assingment t
                          | FUNf    => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "/=46" :: h3 :: set_div_assingment t
                          | _ => h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "/=" :: h3 :: set_div_assingment t
                          end else h1 :: "^^" :: h2 :: "[" :: n :: "]" :: "/=" :: h3 :: set_div_assingment t

(* 34 *)
| h1 :: "^^" :: h2 :: "/=" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "/=34" :: h3 :: "^^" :: h4 :: "[":: m :: "]" :: set_div_assingment t
(* 33 *)
| h1 :: "^^" :: h2 :: "/=" :: h3 :: "^^" :: h4 :: t =>
                           h1 :: "^^" :: h2 :: "/=33" :: h3 :: "^^" :: h4 :: set_div_assingment t
(* 35 *)
| h1 :: "^^" :: h2 :: "/=" :: h3 :: "[":: m :: "]" :: t =>
                           h1 :: "^^" :: h2 :: "/=35" :: h3 :: "[":: m :: "]" :: set_div_assingment t
(* 3 *)
| h1 :: "^^" :: h2 :: "/=" :: h3 :: t => if ( if_who (who h1) LOCAL ) then
                          match who h3 with
                          | NUMBER => h1 :: "^^" :: h2 :: "/=30" :: "$" :: h3 :: set_div_assingment t
                          | LOCAL  => h1 :: "^^" :: h2 :: "/=31" :: h3 :: set_div_assingment t
                          | VAR    => h1 :: "^^" :: h2 :: "/=32" :: h3 :: set_div_assingment t
                          | FUNf    => h1 :: "^^" :: h2 :: "/=36" :: h3 :: set_div_assingment t
                          | _ => h1 :: "^^" :: h2 :: "/=" :: h3 :: set_div_assingment t
                          end else h1 :: "^^" :: h2 :: "/=" :: h3 :: set_div_assingment t
(* 54 *)
| h1 :: "[" :: n :: "]" :: "/=" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: t =>
                          h1 :: "[" :: n :: "]" :: "/=54" :: h2 :: "^^" :: h3 :: "[":: m :: "]" :: set_div_assingment t
(* 53 *)
| h1 :: "[":: n :: "]" :: "/=" :: h2 :: "^^" :: h3 :: t =>
                          h1 :: "[":: n :: "]" :: "/=53" :: h2 :: "^^" :: h3 :: set_div_assingment t
(* 55 *)
| h1 :: "[":: n :: "]" :: "/=" :: h2 :: "[":: m :: "]" :: t =>
                    h1 :: "[":: n :: "]" :: "/=55" :: h2 :: "[":: m :: "]" :: set_div_assingment t
(* 2 *)
| h1 :: "[" :: n :: "]" :: "/=" :: h2 :: t => if ( if_who (who h1) VAR ) then
                          match who h2 with
                          | NUMBER => h1 :: "[" :: n :: "]" :: "/=50" :: "$" :: h2 :: set_div_assingment t
                          | LOCAL  => h1 :: "[" :: n :: "]" :: "/=51" :: h2 :: set_div_assingment t
                          | VAR    => h1 :: "[" :: n :: "]" :: "/=52" :: h2 :: set_div_assingment t
                          | FUNf    => h1 :: "[" :: n :: "]" :: "/=56" :: h2 :: set_div_assingment t
                          | _ => h1 :: "[" :: n :: "]" :: "/=" :: h2 :: set_div_assingment t
                          end else h1 :: "[" :: n :: "]" :: "/=" :: h2 :: set_div_assingment t
(* 6 *)
| h1 :: "/=" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "/=04" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_div_assingment t
                          | LOCAL  => h1 :: "/=14" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_div_assingment t
                          | VAR    => h1 :: "/=24" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_div_assingment t
                          | FUNf    => h1 :: "/=64" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_div_assingment t
                          | _ => h1 :: "/=" :: h2 :: "^^" :: h3 :: "[":: n :: "]" :: set_div_assingment t
                          end
(* 5 *)
| h1 :: "/=" :: h2 :: "^^" :: h3 :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "/=03" :: h2 :: "^^" :: h3 :: set_div_assingment t
                          | LOCAL  => h1 :: "/=13" :: h2 :: "^^" :: h3 :: set_div_assingment t
                          | VAR    => h1 :: "/=23" :: h2 :: "^^" :: h3 :: set_div_assingment t
                          | FUNf    => h1 :: "/=63" :: h2 :: "^^" :: h3 :: set_div_assingment t
                          | _ => h1 :: "/=" :: h2 :: "^^" :: h3 :: set_div_assingment t
                          end
(* 7 *)
| h1 :: "/=" :: h2 :: "[":: n :: "]" :: t => match who h1 with
                          | NUMBER => "$" :: h1 :: "/=05" :: h2 :: "[":: n :: "]" :: set_div_assingment t
                          | LOCAL  => h1 :: "/=15" :: h2 :: "[":: n :: "]" :: set_div_assingment t
                          | VAR    => h1 :: "/=25" :: h2 :: "[":: n :: "]" :: set_div_assingment t
                          | FUNf    => h1 :: "/=65" :: h2 :: "[":: n :: "]" :: set_div_assingment t
                          | _ => h1 :: "/=" :: h2 :: "[":: n :: "]" :: set_div_assingment t
                          end
(* 1 *)
| h1 :: "/=" :: h2 :: t => match who h1, who h2 with
                          | NUMBER, NUMBER => "$" :: h1 :: "/=00" :: "$" :: h2 :: set_div_assingment t
                          | NUMBER, LOCAL  => "$" :: h1 :: "/=01" :: h2 :: set_div_assingment t
                          | NUMBER, VAR    => "$" :: h1 :: "/=02" :: h2 :: set_div_assingment t
                          | NUMBER, FUNf   => "$" :: h1 :: "/=06" :: h2 :: set_div_assingment t
                          | LOCAL, NUMBER => h1 :: "/=10" :: "$" :: h2 :: set_div_assingment t
                          | LOCAL, LOCAL  => h1 :: "/=11" :: h2 :: set_div_assingment t
                          | LOCAL, VAR    => h1 :: "/=12" :: h2 :: set_div_assingment t
                          | LOCAL, FUNf   => h1 :: "/=16" :: h2 :: set_div_assingment t
                          | VAR,   NUMBER => h1 :: "/=20" :: "$" :: h2 :: set_div_assingment t   
                          | VAR,   LOCAL  => h1 :: "/=21" :: h2 :: set_div_assingment t
                          | VAR,   VAR    => h1 :: "/=22" :: h2 :: set_div_assingment t
                          | VAR,   FUNf   => h1 :: "/=26" :: h2 :: set_div_assingment t
                          | FUNf,  NUMBER => h1 :: "/=60" :: "$" :: h2 :: set_div_assingment t   
                          | FUNf,   LOCAL  => h1 :: "/=61" :: h2 :: set_div_assingment t
                          | FUNf,   VAR    => h1 :: "/=62" :: h2 :: set_div_assingment t
                          | FUNf,   FUNf   => h1 :: "/=66" :: h2 :: set_div_assingment t
                          | _, _ => h1 :: "/=" :: h2 :: set_div_assingment t
                          end
| h :: t => h :: set_div_assingment t
end.
