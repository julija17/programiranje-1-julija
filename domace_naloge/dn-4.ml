(*----------------------------------------------------------------------------*
  # 4. domača naloga
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
  ## Slovarji
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
  Na predavanjih in vajah smo si ogledali iskalna drevesa in implementacijo 
  AVL-dreves za predstavitev množic. V tej nalogi morate s pomočjo AVL-dreves 
  implementirati `slovar`, ki preslika ključe tipa `'k` v vrednosti tipa `'v`.
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
  ### Stroga ureditev

  Za predstavitev slovarja potrebujemo strogo ureditev na tipu ključev.
  Najprej definiramo tip `ureditev`, ki predstavlja možne izide
  primerjave dveh elementov, nato pa še modul `UREJEN_TIP`, s katerim
  lahko primerjamo abstraktne elemente.


[*----------------------------------------------------------------------------*)

type ureditev = Less | Equal | Greater

module type UREJEN_TIP = sig
  type t

  val primerjaj : t -> t -> ureditev
end

module INT_UREJEN_TIP : UREJEN_TIP with type t = int = struct
  type t = int

  let primerjaj x y = if x < y then Less else if x > y then Greater else Equal
end

(*----------------------------------------------------------------------------*
  Sestavite modul `STRING_UREJEN_TIP`, ki implementira `UREJEN_TIP` za tip
  `string`.
[*----------------------------------------------------------------------------*)

module STRING_UREJEN_TIP : UREJEN_TIP with type t = string = struct
  type t = string

  let primerjaj x y = 
    if String.compare x y = -1 then Less 
    else if String.compare x y = 1 then Greater
    else Equal
end;;

STRING_UREJEN_TIP.primerjaj "abc" "abd"
(* - : ureditev = Less *)

(*----------------------------------------------------------------------------*
  Za poljuben tip lahko definiramo `razširitev` z najmanjšim in največjim
  elementom. Sestavite parametriziran modul `RAZSIRJEN_UREJEN_TIP`, ki
  sprejme modul, ki implementira signaturo `UREJEN_TIP`, in vrne modul, ki
  implementira signaturo `UREJEN_TIP` za razširjeni tip.
[*----------------------------------------------------------------------------*)

type 'a razsiritev = MinInf | PlusInf | Value of 'a

module RAZSIRJEN_UREJEN_TIP (U : UREJEN_TIP) :
  UREJEN_TIP with type t = U.t razsiritev = struct
  type t = U.t razsiritev

  let primerjaj x y = 
    match x, y with
    | MinInf, MinInf -> Equal
    | PlusInf, PlusInf -> Equal
    | MinInf, _ -> Less
    | PlusInf, _ -> Greater
    | _, MinInf -> Greater
    | _, PlusInf -> Less
    | Value x', Value y' -> U.primerjaj x' y'
end

module LIFTED_INT_UREJEN_TIP = RAZSIRJEN_UREJEN_TIP (INT_UREJEN_TIP);;

LIFTED_INT_UREJEN_TIP.primerjaj MinInf (Value 3)
(* - : ureditev = Less *)

(*----------------------------------------------------------------------------*
  ### AVLSlovar

  Sestavite parametriziran modul `MAKE_SLOVAR`, ki sprejme modul, ki
  implementira `UREJEN_TIP`, in vrne modul s signaturo `SLOVAR`. Vaš slovar
  naj bo implementiran z AVL-drevesi, tako da je vstavljanje in iskanje v
  slovarju v času `O(log n)`.
[*----------------------------------------------------------------------------*)

module type SLOVAR = sig
  type kljuc
  type 'a t

  val prazen : 'a t
  (** Vrne prazen slovar. *)
  val dodaj : kljuc -> 'a -> 'a t -> 'a t
  (** Doda nov par `kljuc`, `vrednost` v slovar. Če ključ v slovarju že obstaja, 
      se njegova vrednost posodobi. *)
  val popravi : kljuc -> ('a option -> 'a option) -> 'a t -> 'a t
  (** Popravi vrednost pod ključem `kljuc` s funkcijo `f`. Če ključ v slovarju
      ne obstaja, se pokliče `f None`, sicer `f (Some vrednost)`. Če je rezultat
      klica `f` enak `None`, se par odstrani iz slovarja, če je rezultat klica 
      `Some v`, se pod ključ `kljuc` zapiše vrednost `v`.*)
  val odstrani : kljuc -> 'a t -> 'a t
  (** Odstrani par s ključem `kljuc` iz slovarja. Če ključa v slovarju ni, naj 
      funkcija vrne prvotni slovar in ne sproži napake. *)
  val velikost : 'a t -> int
  (** Vrne število elementov v slovarju. *)
  val kljuci : 'a t -> kljuc list
  (** Našteje ključe v slovarju v enakem vrstnem redu kot to določa urejenost. *)
  val vrednosti : 'a t -> 'a list
  (** Našteje vrednosti v slovarju v enakem vrstnem redu kot to določa urejenost
      pripadajočih ključev. *)
  val najmanjsi_opt : 'a t -> (kljuc * 'a) option
  (** Vrne najmanjši ključ v slovarju ali `None`, če je slovar prazen. *)
  val najvecji_opt : 'a t -> (kljuc * 'a) option
  (** Vrne največji ključ v slovarju ali `None`, če je slovar prazen. *)
  val poisci_opt : kljuc -> 'a t -> 'a option
  (** Poišče vrednost pod ključem `kljuc`. Če ključ v slovarju ne obstaja,
      vrne `None`. *)
  val iter : (kljuc -> 'a -> unit) -> 'a t -> unit
  (** Izvede funkcijo za vsak par ključ, vrednost v slovarju v enakem vrstnem 
      redu kot ga določa urejenost. *)
  val zlozi : (kljuc -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  (** Zloži slovar z dano funkcijo in začetno vrednostjo. Elementi se obdelajo
      v enakem vrstnem redu kot ga določa urejenost.
  
      Specifično za
      `zlozi f slovar acc = f k_n v_n (... (f k_2 v_2 (f k_1 v_1 acc))...)`
      , kjer so `(k_1, v_1), ..., (k_n, v_n)` pari ključ, vrednost v slovarju 
      urejeni po ključih.
  *)
  val preslikaj : ('a -> 'b) -> 'a t -> 'b t
  (** Preslika vrednosti v slovarju z dano funkcijo. *)
  val preslikaji : (kljuc -> 'a -> 'b) -> 'a t -> 'b t
  (** Preslika vrednosti v slovarju z dano funkcijo, ki poleg vrednosti dobi še
      pripadajoči ključ. *)
  val vsebuje : kljuc -> 'a t -> bool
  (** Preveri, ali slovar vsebuje podan ključ. *)
  val za_vse : (kljuc -> 'a -> bool) -> 'a t -> bool
  (** Preveri, ali za vse pare ključ, vrednost v slovarju velja podan pogoj. *)
  val obstaja : (kljuc -> 'a -> bool) -> 'a t -> bool
  (** Preveri, ali obstaja vsaj en par ključ, vrednost v slovarju, ki izpolnjuje
      podan pogoj. *)
  val v_seznam : 'a t -> (kljuc * 'a) list
  (** Pretvori slovar v seznam parov ključ, vrednost v enakem vrstnem redu kot
      to določa urejenost. *)
  val iz_seznama : (kljuc * 'a) list -> 'a t
  (** Ustvari slovar iz seznama parov ključ, vrednost. Če se ključi v seznamu
      ponavljajo, naj enak ključ obdrži zadnjo vrednost. *)
end


module MAKE_SLOVAR (U : UREJEN_TIP) : SLOVAR with type kljuc = U.t = struct
  type kljuc = U.t
  type 'a t = 
    | Empty 
    | Node of 'a t * (kljuc * 'a) * int * 'a t

  let prazen : 'a t = Empty

  (*Pomožne funkcije za uravnovešanje AVL drevesa*)
  let visina drevo =
    match drevo with
    | Empty -> 0
    | Node (_, (_, _), nivo, _) -> nivo
  
  let naredi_drevo levi vozl desni =
    let nivo = 1 + max (visina levi) (visina desni) in
    Node (levi, vozl, nivo, desni)

  let d_rotacija drevo = 
    match drevo with
    | Node (Node (levi2, vozl2, _, desni2), vozl1, _, desni1) ->
      naredi_drevo levi2 vozl2 (naredi_drevo desni2 vozl1 desni1)
    | drevo -> drevo
  let l_rotacija drevo = 
    match drevo with
    | Node (levi1, vozl1, _, Node (levi2, vozl2, _, desni2)) ->
      naredi_drevo (naredi_drevo levi1 vozl1 levi2) vozl2 desni2
    | drevo -> drevo
  let balance drevo =
    match drevo with
    | Empty -> Empty
    | Node (levi, vozl, _, desni) ->
      let l_visina = visina levi in
      let d_visina = visina desni in
      (*levo poddrevo je preveliko*)
      if l_visina > d_visina + 1 then
        match levi with
        | Empty -> drevo (*ni možno*)
        | Node(levi2, vozl2, _, desni2) -> 
          if visina desni2 > visina levi2 then
            let rot_levi = l_rotacija levi in
            d_rotacija (naredi_drevo rot_levi vozl desni)
          else
            d_rotacija drevo
      (*desno poddrevo je preveliko*)
      else if d_visina > l_visina + 1 then
        match desni with
        | Empty -> drevo
        | Node(levi2, vozl2, _, desni2) -> 
          if visina levi2 > visina desni2 then
            let rot_desni = d_rotacija desni in
            l_rotacija (naredi_drevo levi vozl rot_desni)
          else
            l_rotacija drevo
      else 
        naredi_drevo levi vozl desni

  let rec dodaj kl vred slovar = 
    match slovar with
    | Empty -> Node (Empty, (kl, vred), 1, Empty)
    | Node (levi, (k, v), nivo, desni) ->
      if U.primerjaj kl k = Less then 
        balance (naredi_drevo (dodaj kl vred levi) (k, v) desni)
      else if U.primerjaj kl k = Greater then 
        balance (naredi_drevo levi (k, v) (dodaj kl vred desni))
      else 
        naredi_drevo levi (k, vred) desni
  
  let rec poisci_opt kl slovar = 
    match slovar with
    | Empty -> None
    | Node (levi, (k, v), _, desni) ->
      match U.primerjaj kl k with
      | Less -> poisci_opt kl levi
      | Greater -> poisci_opt kl desni
      | Equal -> Some v

  let rec najmanjsi_opt slovar = 
    match slovar with
    | Empty -> None
    | Node (Empty, vozl, _, _) -> Some vozl
    | Node (levi, _, _, _) -> najmanjsi_opt levi
  let rec najvecji_opt slovar = 
    match slovar with
    | Empty -> None
    | Node (_, vozl, _, Empty) -> Some vozl
    | Node (_, _, _, desni) -> najvecji_opt desni

  let rec odstrani kl slovar = 
    match slovar with
    | Empty -> Empty
    | Node (levi, (k, v), _, desni) -> 
      match U.primerjaj kl k with
      | Less -> 
        balance (naredi_drevo (odstrani kl levi) (k, v) desni)
      | Greater -> 
        balance (naredi_drevo levi (k, v) (odstrani kl desni))
      | Equal ->
        match levi, desni with
        | Empty, _ -> desni
        | _, Empty -> levi
        | _ ->
          let (kl2, v2) = Option.get (najvecji_opt levi) in
          balance (naredi_drevo (odstrani kl2 levi) (kl2, v2) desni)

  let popravi kl f slovar =
    match poisci_opt kl slovar with
    | None -> (
      match f None with
      | None -> slovar
      | Some v -> dodaj kl v slovar
    )
    | Some v -> (
      match f (Some v) with
      | None -> 
        odstrani kl slovar
      | Some vred -> 
        dodaj kl vred slovar
    )      

  let rec velikost slovar = 
    match slovar with
    | Empty -> 0
    | Node (levi, vozl, _, desni) -> 
      velikost levi + 1 + velikost desni

  let rec iter f slovar = 
    match slovar with
    | Empty -> ()
    | Node (levi, (k, v), _, desni) ->
      iter f levi;
      f k v;
      iter f desni

  let rec zlozi f slovar acc = 
    match slovar with
    | Empty -> acc
    | Node (levi, (k, v), _, desni) ->
      let levi_acc = zlozi f levi acc in
      let vozl_acc = f k v levi_acc in
      zlozi f desni vozl_acc

  let kljuci slovar = 
    let f = fun k _ acc -> k :: acc in
    List.rev (zlozi f slovar [])

  let vrednosti slovar = 
    let f = fun _ v acc -> v :: acc in
    List.rev (zlozi f slovar [])

  let rec preslikaj f slovar = 
    match slovar with
    | Empty -> Empty
    | Node (levi, (k, v), _, desni) ->
      naredi_drevo (preslikaj f levi) (k, f v) (preslikaj f desni)

  let rec preslikaji f slovar = 
    match slovar with
    | Empty -> Empty
    | Node (levi, (k, v), _, desni) ->
      naredi_drevo (preslikaji f levi) (k, f k v) (preslikaji f desni)

  let rec vsebuje kl slovar = 
    match slovar with
    | Empty -> false
    | Node (levi, (k, v), _, desni) ->
      match U.primerjaj kl k with
      | Less -> vsebuje kl levi
      | Greater -> vsebuje kl desni
      | Equal -> true

  let rec za_vse f slovar = 
    match slovar with
    | Empty -> true
    | Node (levi, (k, v), _, desni) ->
      if f k v then za_vse f levi && za_vse f desni
      else false

  let rec obstaja f slovar = 
    match slovar with
    | Empty -> false
    | Node (levi, (k, v), _, desni) ->
      if f k v then true
      else obstaja f levi || obstaja f desni

  let v_seznam slovar = 
    let f = fun k v acc -> (k, v) :: acc in
    List.rev (zlozi f slovar [])

  let iz_seznama sez = 
    let rec aux sez drevo =
      match sez with
      | [] -> drevo
      | x :: xs -> 
        aux xs (dodaj (fst x) (snd x) drevo)
    in
    aux sez Empty

end

module SLOVAR_NIZ = MAKE_SLOVAR (STRING_UREJEN_TIP)

let slovar =
  SLOVAR_NIZ.iz_seznama
    [ ("jabolko", "apple"); ("banana", "banana"); ("cesnja", " cherry") ]
  |> SLOVAR_NIZ.dodaj "datelj" "date"
  |> SLOVAR_NIZ.odstrani "banana"
  |> SLOVAR_NIZ.popravi "cesnja" (function
       | None -> Some "cherry"
       | Some v -> Some ("sour " ^ v))
  |> SLOVAR_NIZ.preslikaj String.length
  |> SLOVAR_NIZ.v_seznam

(*----------------------------------------------------------------------------*
  ## Turingovi stroji
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
  Na predavanjih in vajah smo si ogledali Turingove stroje. Pred vami je
  neučinkovito implementiran Turingov stroj. Vaša naloga je, da implementacijo
  s pomočjo slovarjev izboljšate tako, da bo deloval učinkoviteje.
[*----------------------------------------------------------------------------*)

type direction = Left | Right
type state = string

module type TAPE = sig
  type t

  val make : string -> t
  val print : t -> unit
  val read : t -> char
  val move : direction -> t -> t
  val write : char -> t -> t
end

module Tape : TAPE = struct
  type t = { left : char list; right : char list }

  let make str = { left = []; right = str |> String.to_seq |> List.of_seq }

  let print { left; right } =
    List.rev_append left right |> List.to_seq |> String.of_seq |> print_endline;
    print_endline (String.make (List.length left) ' ' ^ "^")

  let read { right } = match right with [] -> ' ' | chr :: _ -> chr

  let move dir { left; right } =
    match (dir, left, right) with
    | Left, ' ' :: left, [] -> { left; right }
    | Left, chr :: left, right -> { left; right = chr :: right }
    | Left, [], right -> { left = []; right = ' ' :: right }
    | Right, [], ' ' :: right -> { left; right }
    | Right, left, chr :: right -> { left = chr :: left; right }
    | Right, left, [] -> { left = ' ' :: left; right = [] }

  let write chr { left; right } =
    match right with
    | [] when chr = ' ' -> { left; right }
    | [] -> { left; right = [ chr ] }
    | _ :: right -> { left; right = chr :: right }
end

let primer_trak =
  Tape.(
    make "ABCDE" |> move Left |> move Left |> move Right |> move Right
    |> move Right |> move Right |> write '!' |> print)

module type MACHINE = sig
  type t

  val make : state -> state list -> t
  val initial : t -> state
  val add_transition : state -> char -> state -> char -> direction -> t -> t
  val step : t -> state -> Tape.t -> (state * Tape.t) option
  val run : t -> state -> unit
  val speed_run : t -> state -> unit
end

module MachineNeucinkovito : MACHINE = struct
  type t = {
    initial : state;
    transitions : (state * char * state * char * direction) list;
  }

  let make initial _states = { initial; transitions = [] }
  let initial { initial } = initial

  let add_transition st chr st' chr' dir tm =
    { tm with transitions = (st, chr, st', chr', dir) :: tm.transitions }

  let step tm st tape =
    let chr = Tape.read tape in
    match
      List.find_opt
        (fun (st', chr', _, _, _) -> st = st' && chr = chr')
        tm.transitions
    with
    | None -> None
    | Some (_, _, st', chr', dir) ->
        Some (st', tape |> Tape.write chr' |> Tape.move dir)

  let run tm str =
    let rec step' (st, tape) =
      (Tape.print tape;
      print_endline st;
      match step tm st tape with
      | None -> ()
      | Some config' -> step' config')
    in
    step' (initial tm, Tape.make str)

  let speed_run tm str =
  let rec step' (st, tape) =
    match step tm st tape with
    | None -> Tape.print tape
    | Some config' -> step' config'
  in
  step' (initial tm, Tape.make str)
end

(*----------------------------------------------------------------------------*
  Sestavite modul `MachineUcinkovito`, ki učinkovito implementira signaturo
  `MACHINE` z uporabo slovarja, ki ste ga implementirali pred tem. Na kratko
  analizirajte časovno zahtevnost operacij `add_transition` in `step` v
  primerjavi z neučinkovito implementacijo.

  Namig:  
  Za dodatne točke je časovna zahtevnost iskanja prehoda v funkciji
  `speed_run` z nekaj preprocesiranja konstantna.
[*----------------------------------------------------------------------------*)

module MachineUcinkovito : MACHINE = struct

  module STANJE_ZNAK : UREJEN_TIP with type t = (state * char) = struct
  type t = (state * char)

  let primerjaj (s1, c1) (s2, c2) = 
    match String.compare s1 s2 with
    | n when n < 0 -> Less
    | 0 -> 
      if c1 < c2 then Less
      else if c1 > c2 then Greater
      else Equal
    | _ -> Greater
  end

  module TRANSITION_SLOVAR = MAKE_SLOVAR (STANJE_ZNAK)

  type t = {
    initial : state;
    transitions : (state * char * direction) TRANSITION_SLOVAR.t;
  }

  let make zacetno _states = 
    { initial = zacetno; transitions = TRANSITION_SLOVAR.prazen }

  let initial { initial } = initial

  let add_transition st chr st' chr' dir tm = 
    { tm with transitions = TRANSITION_SLOVAR.dodaj (st, chr) (st', chr', dir) tm.transitions }

  let step tm st tape = 
    let chr = Tape.read tape in
    match
      TRANSITION_SLOVAR.poisci_opt (st, chr) tm.transitions
    with
    | None -> None
    | Some (st', chr', dir) ->
        Some (st', tape |> Tape.write chr' |> Tape.move dir)

  let run tm stanje =
    let rec step' (st, tape) =
      (Tape.print tape;
      print_endline st;
      match step tm st tape with
      | None -> ()
      | Some config' -> step' config')
    in
    step' (initial tm, Tape.make stanje)

  let speed_run tm stanje =
  let rec step' (st, tape) =
    match step tm st tape with
    | None -> Tape.print tape
    | Some config' -> step' config'
  in
  step' (initial tm, Tape.make stanje)
end


(*----------------------------------------------------------------------------*
  Sestavite Turingov stroj, ki na vhodnem nizu prepozna palindrom (iz `0` in
  `1`). Če je na vhodnem nizu palindrom, naj na koncu na traku zapiše `1`,
  sicer `0`.
[*----------------------------------------------------------------------------*)

let palindrom_stroj : MachineUcinkovito.t = 
  let open MachineUcinkovito in
  let tm = make "qd_zac" [] in
  let tm = tm
    (*prebere znak, ga shrani in se premika do konca desno*)
    |> add_transition "qd_zac" '0' "q0_desno" ' ' Right
    |> add_transition "qd_zac" '1' "q1_desno" ' ' Right
    |> add_transition "qd_zac" ' ' "q_prav" '1' Right

    |> add_transition "q0_desno" '0' "q0_desno" '0' Right
    |> add_transition "q0_desno" '1' "q0_desno" '1' Right
    |> add_transition "q0_desno" ' ' "q0l_isci" ' ' Left

    |> add_transition "q1_desno" '0' "q1_desno" '0' Right
    |> add_transition "q1_desno" '1' "q1_desno" '1' Right
    |> add_transition "q1_desno" ' ' "q1l_isci" ' ' Left
    (*ko pride do konca se obrne in išče shranjen znak*)
    |> add_transition "q0l_isci" '0' "ql_zac" ' ' Left
    |> add_transition "q0l_isci" '1' "ql_narobe" ' ' Left
    |> add_transition "q0l_isci" ' ' "q_prav" '1' Left

    |> add_transition "q1l_isci" '1' "ql_zac" ' ' Left
    |> add_transition "q1l_isci" '0' "ql_narobe" ' ' Left
    |> add_transition "q1l_isci" ' ' "q_prav" '1' Left
    (*prebere znak, ga shrani in se premika do konca levo*)
    |> add_transition "ql_zac" '0' "q0_levo" ' ' Left
    |> add_transition "ql_zac" '1' "q1_levo" ' ' Left
    |> add_transition "ql_zac" ' ' "q_prav" '1' Left

    |> add_transition "q0_levo" '0' "q0_levo" '0' Left
    |> add_transition "q0_levo" '1' "q0_levo" '1' Left
    |> add_transition "q0_levo" ' ' "q0d_isci" ' ' Right
    
    |> add_transition "q1_levo" '0' "q1_levo" '0' Left
    |> add_transition "q1_levo" '1' "q1_levo" '1' Left
    |> add_transition "q1_levo" ' ' "q1d_isci" ' ' Right
    (*ko pride do konca se obrne in išče shranjen znak*)
    |> add_transition "q0d_isci" '0' "qd_zac" ' ' Right
    |> add_transition "q0d_isci" '1' "qd_narobe" ' ' Right
    |> add_transition "q0d_isci" ' ' "q_prav" '1' Right

    |> add_transition "q1d_isci" '1' "qd_zac" ' ' Right
    |> add_transition "q1d_isci" '0' "qd_narobe" ' ' Right
    |> add_transition "q1d_isci" ' ' "q_prav" '1' Right
    (*če ni palindrom, se trak pobriše in izpiše 0*)
    |> add_transition "ql_narobe" '1' "ql_narobe" ' ' Left
    |> add_transition "ql_narobe" '0' "ql_narobe" ' ' Left
    |> add_transition "ql_narobe" ' ' "q_narobe" '0' Left
    
    |> add_transition "qd_narobe" '1' "qd_narobe" ' ' Right
    |> add_transition "qd_narobe" '0' "qd_narobe" ' ' Right
    |> add_transition "qd_narobe" ' ' "q_narobe" '0' Right
  in
  tm

(*----------------------------------------------------------------------------*
  Sestavite Turingov stroj, ki na vhod sprejme niz `n` enic in na koncu na
  traku zapiše `n^2` enic.
[*----------------------------------------------------------------------------*)

let kvadrat_stroj : MachineUcinkovito.t = 
  let open MachineUcinkovito in
  let tm = make "q_zac" [] in
  let tm = tm
    (*gre čez niz in na konec doda ločilo #*)
    |> add_transition "q_zac" '1' "q_zac" '1' Right
    |> add_transition "q_zac" ' ' "q_isci" '#' Left
    (*poišče prvo enko, se obrne in jo zapiše za ločilo*)
    |> add_transition "q_isci" '1' "q_pisi" 'X' Right
    |> add_transition "q_pisi" '#' "q_pisi" '#' Right
    |> add_transition "q_pisi" '1' "q_pisi" '1' Right
    |> add_transition "q_pisi" ' ' "q_obrni" '1' Left
    (*potem se vrne in šteje enke v originalu ter jih kopira za ločilo*)
    (*z X ozačimo zaporedno enico, za katero potem kopiramo n enk za ločilo, ki jih štejemo z Y*)
    |> add_transition "q_obrni" '1' "q_obrni" '1' Left
    |> add_transition "q_obrni" '#' "q_stej" '#' Left
    |> add_transition "q_stej" 'X' "q_stej" 'X' Left
    |> add_transition "q_stej" 'Y' "q_stej" 'Y' Left
    |> add_transition "q_stej" '1' "q_nazajpisi" 'Y' Right
    |> add_transition "q_nazajpisi" 'Y' "q_nazajpisi" 'Y' Right
    |> add_transition "q_nazajpisi" 'X' "q_nazajpisi" 'X' Right
    |> add_transition "q_nazajpisi" '#' "q_pisi" '#' Right
    (*po kopiranju n-terice se resetirajo Y in poišče nov X*)
    |> add_transition "q_stej" ' ' "q_reset" ' ' Right
    |> add_transition "q_reset" 'Y' "q_reset" '1' Right
    |> add_transition "q_reset" 'X' "q_reset" 'X' Right
    |> add_transition "q_reset" '#' "q_isciX" '#' Left
    |> add_transition "q_isciX" '1' "q_isciX" '1' Left
    |> add_transition "q_isciX" 'X' "q_isci" 'X' Left
    |> add_transition "q_isci" 'X' "q_isci" 'X' Left
    (*potem se prejšnji X resetira na 1*)
    |> add_transition "q_pisi" 'X' "q_pisi" '1' Right
    (*ko smo z X prišli do konca pobrišemo original in ločilo*)
    |> add_transition "q_isci" ' ' "q_brisi" ' ' Right
    |> add_transition "q_brisi" 'X' "q_brisi" ' ' Right
    |> add_transition "q_brisi" '1' "q_brisi" ' ' Right
    |> add_transition "q_brisi" '#' "q_konec" ' ' Right
  in
  tm

(*----------------------------------------------------------------------------*
  Sestavite Turingov stroj, ki na začetku na traku sprejme število `n`,
  zapisano v dvojiškem zapisu, na koncu pa naj bo na traku zapisanih
  natanko `n` enic.
[*----------------------------------------------------------------------------*)

let enice_stroj : MachineUcinkovito.t = 
  let open MachineUcinkovito in
  let tm = make "q_zac" [] in
  let tm = tm
    (*gre čez niz in na konec doda ločilo #*)
    |> add_transition "q_zac" '1' "q_zac" '1' Right
    |> add_transition "q_zac" '0' "q_zac" '0' Right
    |> add_transition "q_zac" ' ' "q_isci" '#' Left
    (*poiščemo prvo 1 v dvojiškem številu potem ga zmanjšamo za 1 - 
    spremenimo 1 v 0 in vse 0 v 1*)
    |> add_transition "q_isci" '0' "q_isci" '0' Left
    |> add_transition "q_isci" '1' "q_minus" '0' Right
    |> add_transition "q_minus" '0' "q_minus" '1' Right
    |> add_transition "q_minus" '#' "q_pisi" '#' Right
    (*napišemo eno 1 za ločilo # in se vrnemo*)
    |> add_transition "q_pisi" '1' "q_pisi" '1' Right
    |> add_transition "q_pisi" ' ' "q_nazaj" '1' Left
    |> add_transition "q_nazaj" '1' "q_nazaj" '1' Left
    |> add_transition "q_nazaj" '#' "q_isci" '#' Left
    (*ko dobimo na levi dvojiško število 0, ga pobrišemo*)
    |> add_transition "q_isci" ' ' "q_brisi" ' ' Right
    |> add_transition "q_brisi" '0' "q_brisi" ' ' Right
    |> add_transition "q_brisi" '#' "q_konec" ' ' Right
  in
  tm
(*----------------------------------------------------------------------------*
  Sestavite ravno obratni Turingov stroj, torej tak, ki na začetku na traku
  sprejme število `n` enic, na koncu pa naj bo na traku zapisano število `n`
  v dvojiškem zapisu.
[*----------------------------------------------------------------------------*)

let dvojiski_stroj : MachineUcinkovito.t = 
  let open MachineUcinkovito in
  let tm = make "q_zac" [] in
  let tm = tm
    (*gre čez niz in na konec doda ločilo #*)
    |> add_transition "q_zac" '1' "q_zac" '1' Left
    |> add_transition "q_zac" ' ' "q_isci" '#' Right
    (*poišče prvo 1, jo popravi v 0 in se vrne do ločila #*)
    |> add_transition "q_isci" '0' "q_isci" '0' Right
    |> add_transition "q_isci" '1' "q_nazaj" '0' Left
    |> add_transition "q_nazaj" '0' "q_nazaj" '0' Left
    |> add_transition "q_nazaj" '#' "q_plus" '#' Left
    (* za ločilom poveča dvojiško št. za 1 - prvo 0 spremeni v 1, 
    če pa se začne z enkami, jih spremeni v 0 in na koncu doda 1*)
    |> add_transition "q_plus" '0' "q_vrnise" '1' Right
    |> add_transition "q_plus" '1' "q_plus" '0' Left
    |> add_transition "q_plus" ' ' "q_vrnise" '1' Right
    (* potem se vrnemo do # in ponovno iščemo 1*)
    |> add_transition "q_vrnise" '0' "q_vrnise" '0' Right
    |> add_transition "q_vrnise" '1' "q_vrnise" '1' Right
    |> add_transition "q_vrnise" '#' "q_isci" '#' Right
    (*ko porabimo vse 1 na desni, pobrišemo desno stran*)
    |> add_transition "q_isci" ' ' "q_brisi" ' ' Left
    |> add_transition "q_brisi" '0' "q_brisi" ' ' Left
    |> add_transition "q_brisi" '1' "q_brisi" ' ' Left
    |> add_transition "q_brisi" '#' "q_konec" ' ' Left
  in
  tm

(*----------------------------------------------------------------------------*
  Sestavite Turingov stroj, ki na začetku na traku sprejme oklepaje `(` in
  `)`, `[` in `]` ter `{` in `}`. Stroj naj na traku izpiše `1`, če so
  oklepaji pravilno uravnoteženi in gnezdeni, ter `0` sicer.
[*----------------------------------------------------------------------------*)

let uravnotezeni_oklepaji_stroj : MachineUcinkovito.t = 
  let open MachineUcinkovito in
  let tm = make "q_zac" [] in
  let tm = tm
    (*iščemo najbolj notranji uklepaj*)
    |> add_transition "q_zac" '(' "q_okrogli" '(' Right
    |> add_transition "q_zac" '[' "q_oglati" '[' Right
    |> add_transition "q_zac" '{' "q_zaviti" '{' Right

    |> add_transition "q_okrogli" '(' "q_okrogli" '(' Right
    |> add_transition "q_okrogli" '[' "q_oglati" '[' Right
    |> add_transition "q_okrogli" '{' "q_zaviti" '{' Right

    |> add_transition "q_oglati" '(' "q_okrogli" '(' Right
    |> add_transition "q_oglati" '[' "q_oglati" '[' Right
    |> add_transition "q_oglati" '{' "q_zaviti" '{' Right

    |> add_transition "q_zaviti" '(' "q_okrogli" '(' Right
    |> add_transition "q_zaviti" '[' "q_oglati" '[' Right
    |> add_transition "q_zaviti" '{' "q_zaviti" '{' Right
    (*preverjamo če je naslednji znak pravilni zaklepaj*)
    |> add_transition "q_zac" ')' "q_narobe" ')' Left
    |> add_transition "q_zac" ']' "q_narobe" ']' Left
    |> add_transition "q_zac" '}' "q_narobe" '}' Left

    |> add_transition "q_okrogli" ')' "q_iznici" '0' Left
    |> add_transition "q_oglati" ']' "q_iznici" '0' Left
    |> add_transition "q_zaviti" '}' "q_iznici" '0' Left

    |> add_transition "q_okrogli" ']' "q_narobe" ']' Left
    |> add_transition "q_okrogli" '}' "q_narobe" '}' Left

    |> add_transition "q_oglati" ')' "q_narobe" ')' Left
    |> add_transition "q_oglati" '}' "q_narobe" '}' Left

    |> add_transition "q_zaviti" ')' "q_narobe" ')' Left
    |> add_transition "q_zaviti" ']' "q_narobe" ']' Left

    |> add_transition "q_okrogli" ' ' "q_narobe" ' ' Left
    |> add_transition "q_oglati" ' ' "q_narobe" ' ' Left
    |> add_transition "q_zaviti" ' ' "q_narobe" ' ' Left
    (*že preverjene oklepaje označimo z 0*)
    |> add_transition "q_iznici" '(' "q_zac" '0' Left
    |> add_transition "q_iznici" '[' "q_zac" '0' Left
    |> add_transition "q_iznici" '{' "q_zac" '0' Left
    |> add_transition "q_iznici" '0' "q_iznici" '0' Left

    |> add_transition "q_okrogli" '0' "q_okrogli" '0' Right
    |> add_transition "q_oglati" '0' "q_oglati" '0' Right
    |> add_transition "q_zaviti" '0' "q_zaviti" '0' Right
    |> add_transition "q_zac" '0' "q_zac" '0' Left
    (*če pridemo do napake se vrnemo in pobrišemo vse*)
    |> add_transition "q_narobe" ')' "q_narobe" ')' Left
    |> add_transition "q_narobe" ']' "q_narobe" ']' Left
    |> add_transition "q_narobe" '}' "q_narobe" '}' Left
    |> add_transition "q_narobe" '(' "q_narobe" '(' Left
    |> add_transition "q_narobe" '[' "q_narobe" '[' Left
    |> add_transition "q_narobe" '{' "q_narobe" '{' Left
    |> add_transition "q_narobe" '0' "q_narobe" '0' Left
    |> add_transition "q_narobe" ' ' "qn_brisi" ' ' Right

    |> add_transition "qn_brisi" ')' "qn_brisi" ' ' Right
    |> add_transition "qn_brisi" ']' "qn_brisi" ' ' Right
    |> add_transition "qn_brisi" '}' "qn_brisi" ' ' Right
    |> add_transition "qn_brisi" '(' "qn_brisi" ' ' Right
    |> add_transition "qn_brisi" '[' "qn_brisi" ' ' Right
    |> add_transition "qn_brisi" '{' "qn_brisi" ' ' Right
    |> add_transition "qn_brisi" '0' "qn_brisi" ' ' Right
    |> add_transition "qn_brisi" ' ' "q_konec" '0' Right
    (*če so vsi oklepaji ok pobrišemo vse in napišemo 1, 
    če naletimo na novo skupino oklepajev, ponovimo cikel*)
    |> add_transition "q_zac" ' ' "qp_brisi" ' ' Right
    |> add_transition "qp_brisi" ')' "qn_brisi" ' ' Right
    |> add_transition "qp_brisi" ']' "qn_brisi" ' ' Right
    |> add_transition "qp_brisi" '}' "qn_brisi" ' ' Right
    |> add_transition "qp_brisi" '(' "q_okrogli" '(' Right
    |> add_transition "qp_brisi" '[' "q_oglati" '[' Right
    |> add_transition "qp_brisi" '{' "q_zaviti" '{' Right

    |> add_transition "qp_brisi" '0' "qp_brisi" ' ' Right
    |> add_transition "qp_brisi" ' ' "q_konec" '1' Right
  in
  tm
