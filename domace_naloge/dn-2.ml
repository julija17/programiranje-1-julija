(*----------------------------------------------------------------------------*
 # 2. domača naloga
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 V domači nalogi bomo preučevali _končne avtomate_, enostavne matematične modele
 računanja. Končni avtomati sicer ne morejo opisati vseh možnih izračunov, so pa
 zelo uporabni za prepoznavanje vzorcev v nizih.
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 ## Deterministični končni avtomati
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 _Deterministični končni avtomat_ (_deterministic finite automaton_ oz. DFA) nad
 _abecedo_ $\Sigma$ je sestavljen iz _množice stanj_ $Q$ ter _prehodne funkcije_
 $\delta : Q \times \Sigma \rightharpoonup Q$ med njimi. Avtomat začne v enem
 izmed možnih stanj $q_0$, nato pa glede na trenutno stanje in trenutni simbol
 preide v neko novo stanje in od tam nadaljuje z naslednjim znakom. Če ob
 pregledu celotnega niza konča v enem od _sprejemnih stanj_ $F \subseteq Q$, je
 niz sprejet, sicer pa ni. Prehodna funkcija $\delta$ je delno definirana. Če za
 trenutno stanje in simbol prehod ne obstaja, avtomat niz zavrne.

 Za primer si oglejmo avtomat, ki sprejema nize, sestavljene iz ničel in enic, v
 katerih je število enic deljivo s tri. Tak avtomat predstavimo z naslednjim
 diagramom, na katerem je začetno stanje označeno s puščico, sprejemna stanja pa
 so dvojno obkrožena.

 ![DFA](slike/dfa.png)

 V tem avtomatu je abeceda $\Sigma = \{ 0, 1\}$, potrebujemo pa tri stanja, za
 vsak ostanek enega, zato je $Q = \{ q_0, q_1, q_2 \}$. Začetno stanje je $q_0$,
 ki je hkrati tudi edino sprejemno stanje. Prehodna funkcija je definirana kot:

 | $\delta$ | $0$   | $1$   |
 | -------- | ----- | ----- |
 | $q_0$    | $q_0$ | $q_1$ |
 | $q_1$    | $q_1$ | $q_2$ |
 | $q_2$    | $q_2$ | $q_0$ |

 Če avtomat na primer prejme niz $10011$, bo prehajal skozi stanja:
 - Začetno stanje: $q_0$
 - Prebere $1$: prehod v $q_1$
 - Prebere $0$: stanje ostane $q_1$
 - Prebere $0$: stanje ostane $q_1$
 - Prebere $1$: prehod v $q_2$
 - Prebere $1$: prehod v $q_0$

 Ker je stanje $q_0$ sprejemno, avtomat niz sprejme.
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 ### Modul `DFA`
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Pri implementaciji se bomo omejili na avtomate, ki delujejo nad znaki angleške
 abecede, stanja pa bomo zaradi preglednosti predstavili kar z nizi. Take
 avtomate predstavimo s signaturo `DFA_SIG`:
[*----------------------------------------------------------------------------*)

module type DFA_SIG = sig
  type stanje = string
  type t

  (* Funkcije za grajenje *)
  (* Argument tipa [bool] pove, ali naj bo dodano stanje sprejemno *)
  val ustvari : stanje -> bool -> t
  val dodaj_stanje : stanje -> bool -> t -> t
  val dodaj_prehod : stanje -> char -> stanje -> t -> t

  (* Funkcije za poizvedovanje *)
  val seznam_stanj : t -> stanje list
  val zacetno_stanje : t -> stanje
  val je_sprejemno_stanje : t -> stanje -> bool
  val prehodna_funkcija : t -> stanje -> char -> stanje option
  val seznam_prehodov : t -> (stanje * char * stanje) list
end

(*----------------------------------------------------------------------------*
 Napišite modul `DFA`, ki zadošča zgornji signaturi.
[*----------------------------------------------------------------------------*)

module DFA : DFA_SIG = struct
  type stanje = string
  type enota = {
    ime : stanje;
    sprejem : bool
  }
  type t = {
    stanja : enota list;
    zacetno : stanje;
    prehodi : (stanje * char * stanje) list
  }

  let ustvari ime1 sprejem1 = {
    stanja = [{ime = ime1; sprejem = sprejem1}];
    zacetno = ime1;
    prehodi = []
    }
  let dodaj_stanje ime1 sprejem1 avtomat = 
    let novo = {ime = ime1; sprejem = sprejem1} in
    { avtomat with stanja = novo :: avtomat.stanja }
  let dodaj_prehod ime1 znak ime2 avtomat = 
    { avtomat with prehodi = (ime1, znak, ime2) :: avtomat.prehodi }

  let seznam_stanj avtomat = 
    List.map (fun e -> e.ime) avtomat.stanja
  let zacetno_stanje avtomat = 
    avtomat.zacetno
  let je_sprejemno_stanje avtomat ime1 = 
    let enota1 = List.find (fun e -> e.ime = ime1) avtomat.stanja in
    enota1.sprejem
  let prehodna_funkcija avtomat ime1 znak = 
    let pomozna skok =
      match skok with
      | (s1, z, s2) when s1 = ime1 && z = znak -> Some s2
      | _ -> None
    in
    List.find_map pomozna avtomat.prehodi
  let seznam_prehodov avtomat = 
    avtomat.prehodi
end 

(*----------------------------------------------------------------------------*
 Primer zgornjega avtomata bi lahko zapisali kot:
[*----------------------------------------------------------------------------*)

let enke_deljive_s_3 = DFA.(
    ustvari "q0" true
    |> dodaj_stanje "q1" false
    |> dodaj_stanje "q2" false
    |> dodaj_prehod "q0" '0' "q0"
    |> dodaj_prehod "q1" '0' "q1"
    |> dodaj_prehod "q2" '0' "q2"
    |> dodaj_prehod "q0" '1' "q1"
    |> dodaj_prehod "q1" '1' "q2"
    |> dodaj_prehod "q2" '1' "q0"
)
(* val enke_deljive_s_3 : DFA.t = <abstr> *)

(*----------------------------------------------------------------------------*
 ### Izpis avtomata
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `dot_of_dfa : DFA.t -> string`, ki vrne zapis avtomata v
 formatu `dot`. Na ta način si lahko avtomat ogledate s programom
 [GraphViz](https://graphviz.org) ali kar v [spletnem
 pregledovalniku](https://www.devtoolsdaily.com/graphviz/).
[*----------------------------------------------------------------------------*)

let dot_of_dfa avtomat = 
  let uvod = "digraph DFA {\nrankdir=LR;\nsize=\"8,5\"\n" in

  let rec razvrsti_stanja i sprejemni navadni =
    if i = List.length (DFA.seznam_stanj avtomat) then
      let sp_node = "node [shape = doublecircle]; " ^ (String.concat " " sprejemni) ^ ";\n" in
      let nav_node = "node [shape = circle]; " ^ (String.concat " " navadni) ^ ";\n" in
      sp_node ^ nav_node
    else 
      let stanje = List.nth (DFA.seznam_stanj avtomat) i in
      if DFA.je_sprejemno_stanje avtomat stanje then
        razvrsti_stanja (i+1) (stanje :: sprejemni) navadni
      else
        razvrsti_stanja (i+1) sprejemni (stanje :: navadni)
  in
  let nodes = razvrsti_stanja 0 [] [] in

  let prehod_smer (s1, z, s2) = 
    s1 ^ " -> " ^ s2 ^ " [label=\"" ^ (String.make 1 z) ^ "\"];\n"
  in
  let smeri_sez = List.map prehod_smer (DFA.seznam_prehodov avtomat) in
  let smeri = String.concat "" smeri_sez in
  uvod ^ nodes ^ "\"\" [shape=none];\n\"\"-> " ^ (DFA.zacetno_stanje avtomat) ^ ";\n" ^ smeri ^ "}"

let () = enke_deljive_s_3 |> dot_of_dfa |> print_endline

(*----------------------------------------------------------------------------*
 ### Sprejemanje niza
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Sestavite funkcijo `dfa_sprejema : DFA.t -> string -> bool`, ki preveri, ali
 avtomat sprejme podani niz.
[*----------------------------------------------------------------------------*)

let dfa_sprejema avtomat niz = 
  let rec aux i stanje =
    if i = String.length niz then
      DFA.je_sprejemno_stanje avtomat stanje
    else
      match DFA.prehodna_funkcija avtomat stanje niz.[i] with
      | None -> false
      | Some s -> aux (i+1) s
  in
  aux 0 (DFA.zacetno_stanje avtomat)



let nizi =
  let razsiri nizi = List.map ((^) "0") nizi @ List.map ((^) "1") nizi in
  let razsiri_zadnjega =
    function
    | [] -> []
    | (zadnji :: _) as vsi -> razsiri zadnji :: vsi
  in
  let rec loop n vsi =
    if n = 0 then
      vsi |> List.rev |> List.flatten
    else
      loop (n - 1) (razsiri_zadnjega vsi)
  in
  loop 5 [[""]]
(* val nizi : string list =
  [""; "0"; "1"; "00"; "01"; "10"; "11"; "000"; "001"; "010"; "011"; "100";
   "101"; "110"; "111"; "0000"; "0001"; "0010"; "0011"; "0100"; "0101";
   "0110"; "0111"; "1000"; "1001"; "1010"; "1011"; "1100"; "1101"; "1110";
   "1111"; "00000"; "00001"; "00010"; "00011"; "00100"; "00101"; "00110";
   "00111"; "01000"; "01001"; "01010"; "01011"; "01100"; "01101"; "01110";
   "01111"; "10000"; "10001"; "10010"; "10011"; "10100"; "10101"; "10110";
   "10111"; "11000"; "11001"; "11010"; "11011"; "11100"; "11101"; "11110";
   "11111"] *)

let primer_dfa = List.filter (dfa_sprejema enke_deljive_s_3) nizi
(* val primer_dfa : string list =
  [""; "0"; "00"; "000"; "111"; "0000"; "0111"; "1011"; "1101"; "1110";
   "00000"; "00111"; "01011"; "01101"; "01110"; "10011"; "10101"; "10110";
   "11001"; "11010"; "11100"] *)

(*----------------------------------------------------------------------------*
 ## Nedeterministični končni avtomati
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Nedeterministični končni avtomati (_nondeterministic finite automaton_ oz. NFA)
 se od determinističnih razlikujejo v dveh pogledih:
 - dopuščajo prazne prehode med stanji, torej prehode, ki se zgodijo brez branja
 simbola iz niza,
 - iz enega stanja lahko obstaja več prehodov za isti simbol.

 Prehodno funkcijo $\delta$ tako definiramo kot $\delta : Q \times (\Sigma \cup
 \{ \varepsilon \}) \rightarrow \mathcal{P}(Q)$, kjer simbol $\varepsilon$
 predstavlja prazen prehod, $\mathcal{P}(Q)$ pa je potenčna množica množice
 stanj $Q$. Vsak deterministični končni avtomat je tudi nedeterminističen končni
 avtomat, velja pa tudi obratno. Za vsak nedeterministični končni avtomat lahko
 ustvarimo ustrezen deterministični končni avtomat, ki sprejema iste nize
 (namig: za stanja ustreznega DFA vzamemo podmnožice stanj NFA).

 Avtomat sprejme niz, če obstaja pot, ki ji sledimo po prehodih z zaporednimi
 znaki niza ali praznih prehodih, tako da začnemo v začetnem stanju in končamo v
 enem od sprejemnih stanj.

 Na primer, vzemimo avtomat, ki sprejema nize, sestavljene iz ničel in enic, v
 katerih je ali število enic ali število ničel deljivo s 3. Tak avtomat je
 sestavljen iz začetnega stanja, s praznim prehodom v eno kopijo prejšnjega
 avtomata ter še enim praznim prehodom v drugo kopijo, v kateri zamenjamo vlogi
 znakov.

 ![NFA](slike/nfa.png)

 Kot pri primeru za deterministični avtomat je avtomat definiran nad abecedo
 $\Sigma = \{ 0, 1\}$, stanj je tokrat sedem, poleg začetnega še po tri v vsaki
 _kopiji_ avtomata iz prvega primera. Tako je $Q = \{ q_0, q_{00}, q_{01},
 q_{02}, q_{10}, q_{11}, q_{12} \}$. Začetno stanje je $q_0$, sprejemni pa sta
 $q_{00}$ in $q_{10}$. Prehodna funkcija je definirana kot:

 | $\delta$   | `0`          | `1`          | $\varepsilon$ |
 | ---------- | ------------ | ------------ | ------------- |
 | $q_0$      | $\emptyset$  | $\emptyset$  | $\{q_{00}\}$  |
 | $q_0$      | $\emptyset$  | $\emptyset$  | $\{q_{10}\}$  |
 | $q_{00}$   | $\{q_{01}\}$ | $\{q_{00}\}$ | $\emptyset$   |
 | $q_{01}$   | $\{q_{02}\}$ | $\{q_{01}\}$ | $\emptyset$   |
 | $q_{02}$   | $\{q_{00}\}$ | $\{q_{02}\}$ | $\emptyset$   |
 | $q_{10}$   | $\{q_{10}\}$ | $\{q_{11}\}$ | $\emptyset$   |
 | $q_{11}$   | $\{q_{11}\}$ | $\{q_{12}\}$ | $\emptyset$   |
 | $q_{12}$   | $\{q_{12}\}$ | $\{q_{10}\}$ | $\emptyset$   |

 Če avtomat prejme niz `10011`, bo prehajal skozi stanja:
 - Začetno stanje: $q_0$
 - Pred branjem znaka `1` se lahko po praznih prehodih premakne v stanji
 $q_{00}$ in $q_{10}$, tako da so njegova možna stanja $\{q_0, q_{00}, q_{10}\}$
 - Prebere `1`: vsa tri možna stanja se premaknejo, če se lahko (stanje $q_0$
 nima možnega premika), tako so možna stanja $\{q_{01}, q_{10}\}$
 - Pred branjem novega znaka se zopet lahko vsa možna stanja premaknejo po
 praznih prehodih, a ker teh ni, ostaneta možni stanji $\{q_{01}, q_{10}\}$
 - Prebere `0`: po prehodih so možna stanja $\{q_{01}, q_{11}\}$
 - Prazni premiki in branje `0`: možna stanja $\{q_{02}, q_{11}\}$
 - Prazni premiki in branje `1`: možna stanja $\{q_{02}, q_{12}\}$
 - Prazni premiki in branje `1`: možna stanja $\{q_{02}, q_{10}\}$
 - Prazni premiki: možna stanja ostanejo $\{q_{02}, q_{10}\}$

 Ker je stanje $q_{10}$ sprejemno, avtomat niz sprejme.
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 ### Modul `NFA`
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Nedeterministične avtomate predstavimo s signaturo `NFA_SIG`, podobno zgornji:
[*----------------------------------------------------------------------------*)

module type NFA_SIG = sig
  type stanje = string
  type t

  (* Funkcije za grajenje *)
  val ustvari : stanje -> bool -> t
  val dodaj_stanje : stanje -> bool -> t -> t
  val dodaj_prehod : stanje -> char -> stanje -> t -> t
  val dodaj_prazen_prehod : stanje -> stanje -> t -> t

  (* Funkcije za poizvedovanje *)
  val seznam_stanj : t -> stanje list
  val zacetno_stanje : t -> stanje
  val je_sprejemno_stanje : t -> stanje -> bool
  val prehodna_funkcija : t -> stanje -> char option -> stanje list
  val seznam_prehodov : t -> (stanje * char option * stanje) list
end

(*----------------------------------------------------------------------------*
 Napišite modul `NFA`, ki zadošča zgornji signaturi.
[*----------------------------------------------------------------------------*)

module NFA : NFA_SIG = struct
  type stanje = string
  type enota = {
    ime : stanje;
    sprejem : bool
  }
  type t = {
    stanja : enota list;
    zacetno : stanje;
    prehodi : (stanje * char option * stanje) list;
  }

  let ustvari ime1 sprejem1 = {
    stanja = [{ime = ime1; sprejem = sprejem1}];
    zacetno = ime1;
    prehodi = []
    }
  let dodaj_stanje ime1 sprejem1 avtomat = 
    let novo = {ime = ime1; sprejem = sprejem1} in
    { avtomat with stanja = novo :: avtomat.stanja }
  let dodaj_prehod ime1 znak ime2 avtomat = 
    { avtomat with prehodi = (ime1, Some znak, ime2) :: avtomat.prehodi }
  let dodaj_prazen_prehod ime1 ime2 avtomat = 
    { avtomat with prehodi = (ime1, None, ime2) :: avtomat.prehodi }

  let seznam_stanj avtomat = 
    List.map (fun e -> e.ime) avtomat.stanja
  let zacetno_stanje avtomat = 
    avtomat.zacetno
  let je_sprejemno_stanje avtomat ime1 = 
    let enota1 = List.find (fun e -> e.ime = ime1) avtomat.stanja in
    enota1.sprejem
  let prehodna_funkcija avtomat ime1 znak = 
    let pomozna skok =
      match skok with
      | (s1, None, s2) when s1 = ime1 && znak = None-> Some s2
      | (s1, z, s2) when s1 = ime1 && z = znak -> Some s2
      | _ -> None
    in
    List.filter_map pomozna avtomat.prehodi
  let seznam_prehodov avtomat  = 
  avtomat.prehodi

end

(*----------------------------------------------------------------------------*
 Primer zgornjega avtomata bi lahko zapisali kot:
[*----------------------------------------------------------------------------*)

let enke_ali_nicle_deljive_s_3 = NFA.(
    ustvari "q0" false
    |> dodaj_stanje "q00" true
    |> dodaj_stanje "q01" false
    |> dodaj_stanje "q02" false
    |> dodaj_prehod "q00" '0' "q01"
    |> dodaj_prehod "q01" '0' "q02"
    |> dodaj_prehod "q02" '0' "q00"
    |> dodaj_prehod "q00" '1' "q00"
    |> dodaj_prehod "q01" '1' "q01"
    |> dodaj_prehod "q02" '1' "q02"
    |> dodaj_stanje "q10" true
    |> dodaj_stanje "q11" false
    |> dodaj_stanje "q12" false
    |> dodaj_prehod "q10" '1' "q11"
    |> dodaj_prehod "q11" '1' "q12"
    |> dodaj_prehod "q12" '1' "q10"
    |> dodaj_prehod "q10" '0' "q10"
    |> dodaj_prehod "q11" '0' "q11"
    |> dodaj_prehod "q12" '0' "q12"
    |> dodaj_prazen_prehod "q0" "q00"
    |> dodaj_prazen_prehod "q0" "q10"
)
(* val enke_ali_nicle_deljive_s_3 : NFA.t = <abstr> *)

(*----------------------------------------------------------------------------*
 ### Izpis avtomata
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `dot_of_nfa : NFA.t -> string`, ki vrne zapis avtomata v
 formatu `dot`.
[*----------------------------------------------------------------------------*)

let dot_of_nfa avtomat = 
  let uvod = "digraph DFA {\nrankdir=LR;\nsize=\"8,5\"\n" in

  let rec razvrsti_stanja i sprejemni navadni =
    if i = List.length (NFA.seznam_stanj avtomat) then
      let sp_node = "node [shape = doublecircle]; " ^ (String.concat " " sprejemni) ^ ";\n" in
      let nav_node = "node [shape = circle]; " ^ (String.concat " " navadni) ^ ";\n" in
      sp_node ^ nav_node
    else 
      let stanje = List.nth (NFA.seznam_stanj avtomat) i in
      if NFA.je_sprejemno_stanje avtomat stanje then
        razvrsti_stanja (i+1) (stanje :: sprejemni) navadni
      else
        razvrsti_stanja (i+1) sprejemni (stanje :: navadni)
  in
  let nodes = razvrsti_stanja 0 [] [] in

  let prehod_smer (s1, nekaj, s2) = 
    match (s1, nekaj, s2) with
    | (s1, None, s2) -> s1 ^ " -> " ^ s2 ^ " [label=\"ɛ\"];\n"
    | (s1, Some z, s2) -> s1 ^ " -> " ^ s2 ^ " [label=\"" ^ (String.make 1 z) ^ "\"];\n"
  in
  let smeri_sez = List.map prehod_smer (NFA.seznam_prehodov avtomat) in
  let smeri = String.concat "" smeri_sez in
  uvod ^ nodes ^ "\"\" [shape=none];\n\"\"-> " ^ (NFA.zacetno_stanje avtomat) ^ ";\n" ^ smeri ^ "}"



let () = enke_ali_nicle_deljive_s_3 |> dot_of_nfa |> print_endline

(*----------------------------------------------------------------------------*
 ### Sprejemanje niza
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Sestavite funkcijo `nfa_sprejema : NFA.t -> string -> bool`, ki preveri, ali
 avtomat sprejme podani niz.
[*----------------------------------------------------------------------------*)

let rec prazni_prehodi avtomat sez_stanj =
  let novi = List.flatten (List.map (fun s -> NFA.prehodna_funkcija avtomat s None) sez_stanj) in
  let zdruzeni = List.sort_uniq compare (sez_stanj @ novi) in
  if zdruzeni = sez_stanj then
    zdruzeni
  else
    prazni_prehodi avtomat zdruzeni

let znak_prehodi avtomat znak sez_stanj =
  List.flatten (List.map (fun s -> NFA.prehodna_funkcija avtomat s (Some znak)) sez_stanj)

let nfa_sprejema avtomat niz = 
  let zacetni = prazni_prehodi avtomat [NFA.zacetno_stanje avtomat] in
  let rec po_nizu i sez_stanj =
    if i = String.length niz then
      sez_stanj
    else
      let stanja1 = znak_prehodi avtomat niz.[i] sez_stanj in
      let stanja2 = prazni_prehodi avtomat stanja1 in
      po_nizu (i+1) stanja2
  in
  let koncni = po_nizu 0 zacetni in
  List.exists (fun s -> NFA.je_sprejemno_stanje avtomat s) koncni



let primer_nfa = List.filter (nfa_sprejema enke_ali_nicle_deljive_s_3) nizi
(* val primer_nfa : string list =
  [""; "0"; "1"; "00"; "11"; "000"; "111"; "0000"; "0001"; "0010"; "0100";
   "0111"; "1000"; "1011"; "1101"; "1110"; "1111"; "00000"; "00011"; "00101";
   "00110"; "00111"; "01001"; "01010"; "01011"; "01100"; "01101"; "01110";
   "10001"; "10010"; "10011"; "10100"; "10101"; "10110"; "11000"; "11001";
   "11010"; "11100"; "11111"] *)

(*----------------------------------------------------------------------------*
 ## Regularni izrazi
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Regularni izrazi so formalni opisi jezikov (množic nizov) nad abecedo $\Sigma$.
 Uporabljajo se za kompaktno opisovanje vzorcev, ki jim morajo nizi ustrezati.
 Rečemo, da niz *ustreza* regularnemu izrazu, če ga lahko zgradimo z
 upoštevanjem pravil, ki jih določa ta izraz.

 Regularni izrazi so sestavljeni iz osnovnih elementov in operacij:

 - $\emptyset$ ne ustreza nobenemu jeziku,
 - $\varepsilon$ ustreza prazen niz,
 - za vsak znak $a \in \Sigma$, izrazu $a$ ustreza natanko natanko niz dolžine
 1, sestavljenem le iz znaka $a$,
 - *uniji* $r_1 \mid r_2$ ustreza vsem nizom, ki ustrezajo $r_1$ ali $r_2$,
 - *stiku* $r_1 r_2$ ustrezajo vsi nizi oblike $s_1 s_2$, kjer $s_1$ ustreza
 $r_1$ ter $s_2$ ustreza $r_2$,
 - *Kleenejevemu zaprtju* $r^*$ ustrezajo vsi nizi oblike $s_1 s_2 \cdots s_n$
 za nek $n$ (vključno s praznim nizom), kjer vsak izmed nizov $s_i$ ustreza $r$.

 Za primer si oglejmo regularni izraz $a^* b$. Ta izraz je sestavljen kot stik
 izrazov $a^*$ in $b$ in tako sprejme vse nize, ki se začnejo s poljubnim
 številom ponovitev (lahko nič) znaka $a$ in končajo z znakom $b$. Izrazu tako
 ustreza niz $aaab$, niz $aaabb$ pa ne. Nize, v katerih je število enk deljivo s
 tri, bi lahko opisali z regularnim izrazom $0^*( 10^*10^*10^* )^*$.

 Regularne izraze bomo implementirali z algebrajskim tipom, ki ima za
 konstruktorje zgoraj naštete osnovne elemente in operacije na regularnih
 izrazih.
[*----------------------------------------------------------------------------*)

type regex =
  | Empty
  | Eps
  | Char of char
  | Union of regex * regex
  | Concat of regex * regex
  | Star of regex

let re_enke_deljive_s_3 =
  let poljubno_nicel = Star (Char '0') in
  let enka_in_poljubno_nicel = Concat (Char '1', poljubno_nicel) in
  Concat (poljubno_nicel, Star (Concat (Concat (enka_in_poljubno_nicel, enka_in_poljubno_nicel), enka_in_poljubno_nicel)))
(* val re_enke_deljive_s_3 : regex =
  Concat (Star (Char '0'),
   Star
    (Concat
      (Concat (Concat (Char '1', Star (Char '0')),
        Concat (Char '1', Star (Char '0'))),
      Concat (Char '1', Star (Char '0'))))) *)

(*----------------------------------------------------------------------------*
 ### Izpisovanje
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `string_of_regex : Regex.t -> string`, ki regularni izraz
 predstavi z nizom. Pri tem poskusite zapisati čim manj oklepajev, upoštevaje
 to, da ima Kleenejevo zaprtje najvišjo prioriteto, sledi stik, nato pa unija.
 Poleg tega sta stik in unija asociativni operaciji.
[*----------------------------------------------------------------------------*)

let prioriteta =
  function
  | Empty | Eps | Char _ -> 3
  | Union _ -> 0
  | Concat _ -> 1
  | Star _ -> 2

let rec string_of_regex regniz = 
  match regniz with
  | Empty -> ""
  | Eps -> ""
  | Char c -> String.make 1 c
  | Union (r1, r2) -> string_of_regex r1 ^ "|" ^ string_of_regex r2
  | Concat (r1, r2) -> 
      let s1 = string_of_regex r1 in
      let s2 = string_of_regex r2 in
      let p1 = prioriteta r1 in
      let p2 = prioriteta r2 in
      if p1 < 1 && p2 < 1 then "(" ^ s1 ^ ")("  ^ s2 ^ ")"
      else if p1 < 1 then "(" ^ s1 ^ ")" ^ s2
      else if p2 < 1 then s1 ^ "("  ^ s2 ^ ")"
      else s1 ^ s2
  | Star r -> 
      let s = string_of_regex r in
      if prioriteta r < 2 then "(" ^ s ^ ")*"
      else s ^ "*"


let primer_regex_1 = string_of_regex re_enke_deljive_s_3
(* val primer_regex_1 : string = "0*(10*10*10*)*" *)

(*----------------------------------------------------------------------------*
 ### Sprejeti nizi
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Napišite funkcijo `regex_sprejema: regex -> string -> bool`, ki preveri, ali
 dan niz ustreza regularnemu izrazu.
[*----------------------------------------------------------------------------*)

let rec regex_sprejema reg niz = 
  match reg with
  | Empty -> false
  | Eps -> if niz = "" then true else false
  | Char c -> if niz = String.make 1 c then true else false
  | Union (r1, r2) -> 
    regex_sprejema r1 niz || regex_sprejema r2 niz

  | Concat (r1, r2) -> 
      let concat_sprejema r1 r2 niz =
        let rec aux i =
          if i > String.length niz then
            false
          else
            let s1 = String.sub niz 0 i in
            let s2 = String.sub niz i (String.length niz - i) in
            if regex_sprejema r1 s1 && regex_sprejema r2 s2 then
              true
            else
              aux (i+1)
        in
        aux 0
      in
      concat_sprejema r1 r2 niz

  | Star r -> 
    let rec star_sprejema r niz =
      if niz = "" then true 
      else
        let rec aux i =
          if i > String.length niz then
            false
          else
            let s1 = String.sub niz 0 i in
            let s2 = String.sub niz i (String.length niz - i) in
            if regex_sprejema r s1 && star_sprejema r s2 then
              true
            else
              aux (i+1)
        in
        aux 1
    in
    star_sprejema r niz





let primer_regex_2 = regex_sprejema re_enke_deljive_s_3 "10011"
(* val primer_regex_2 : bool = true *)

let primer_regex_3 = regex_sprejema re_enke_deljive_s_3 "100111"
(* val primer_regex_3 : bool = false *)

(*----------------------------------------------------------------------------*
 ### Od regularnega izraza do avtomata
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Izkaže se, da med regularnimi izrazi in nedeterminističnimi končnimi avtomati
 obstaja ekvivalenca. Za vsak izraz obstaja ustrezen avtomat, ki sprejema iste
 nize in obratno. Mi bomo ekvivalenco pokazali le v eno stran tako, da bomo za
 vsak konstruktor regularnih izrazov definirali ustrezno konstrukcijo na končnih
 avtomatih.
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Definirajte avtomat `prazen_nfa: NFA.t`, ki ne sprejme nobenega niza.
[*----------------------------------------------------------------------------*)

let prazen_nfa = NFA.(
  ustvari "q0" false
)

let primer_regex_4 = List.filter (nfa_sprejema prazen_nfa) nizi
(* val primer_regex_4 : string list = [] *)

(*----------------------------------------------------------------------------*
 Definirajte avtomat `epsilon_nfa: NFA.t`, ki sprejme natanko prazen niz.
[*----------------------------------------------------------------------------*)

let epsilon_nfa = NFA.(
  ustvari "q0" true
)

let primer_regex_5 = List.filter (nfa_sprejema epsilon_nfa) nizi
(* val primer_regex_5 : string list = [""] *)

(*----------------------------------------------------------------------------*
 Definirajte funkcijo `znak_nfa: char -> NFA.t`, ki vrne avtomat, ki sprejme
 natanko niz dolžine ena z znakom v argumentu.
[*----------------------------------------------------------------------------*)

let znak_nfa znak = NFA.(
  ustvari "q0" false
  |> dodaj_stanje "q1" true
  |> dodaj_prehod "q0" znak "q1"
)

let primer_regex_6 = List.filter (nfa_sprejema (znak_nfa '0')) nizi
(* val primer_regex_6 : string list = ["0"] *)

(*----------------------------------------------------------------------------*
 Definirajte funkcijo `unija_nfa: NFA.t -> NFA.t -> NFA.t`, ki vrne avtomat, ki
 sprejme nize sprejete s katerim koli izmed avtomatov v argumentih.
[*----------------------------------------------------------------------------*)

let unija_nfa avt1 avt2 = 
  let stanja1 = NFA.seznam_stanj avt1 in
  let stanja2 = NFA.seznam_stanj avt2 in
  (*Najprej dodamo vsa stanja iz prevega avtomata in potem takoj še vsa iz drugega avtomata
  Za ime vsakega stanja dodamo indeks, da vemo iz katerega avtomata je prišlo.*)
  let rec pisi_stanja i avto_index seznam avto unija =
    if avto_index = "u2" && i = List.length seznam then 
      unija
    else if i = List.length seznam then
      pisi_stanja 0 "u2" stanja2 avt2 unija
    else
      let trenutno = List.nth seznam i in
      let nova_unija = NFA.dodaj_stanje (trenutno ^ avto_index) (NFA.je_sprejemno_stanje avto trenutno) unija in
      pisi_stanja (i+1) avto_index seznam avto nova_unija
  in
  let unija = pisi_stanja 0 "u1" stanja1 avt1 NFA.(ustvari "q" false) in
  (*Dodamo prehode*)
  let prehodi1 = NFA.seznam_prehodov avt1 in
  let prehodi2 = NFA.seznam_prehodov avt2 in
  let rec pisi_prehode i avto_index seznam avto unija =
    if avto_index = "u2" && i = List.length seznam then 
      unija
    else if i = List.length seznam then
      pisi_prehode 0 "u2" prehodi2 avt2 unija
    else
      match List.nth seznam i with
      | (ime1, None, ime2) -> 
        let nova_unija = NFA.dodaj_prazen_prehod (ime1 ^ avto_index) (ime2 ^avto_index) unija in
        pisi_prehode (i+1) avto_index seznam avto nova_unija
      | (ime1, Some znak, ime2) -> 
        let nova_unija = NFA.dodaj_prehod (ime1 ^ avto_index) znak (ime2 ^avto_index) unija in
        pisi_prehode (i+1) avto_index seznam avto nova_unija
  in
  let unija = pisi_prehode 0 "u1" prehodi1 avt1 unija in
  (*Dodamo prazne prehode iz začetnega stanja, da povežemo oba avtomata.*)
  let unija = NFA.dodaj_prazen_prehod "q" (NFA.zacetno_stanje avt1 ^ "u1") unija in
  let unija = NFA.dodaj_prazen_prehod "q" (NFA.zacetno_stanje avt2 ^ "u2") unija in
  unija
  

let primer_regex_7 = List.filter (nfa_sprejema (unija_nfa epsilon_nfa (znak_nfa '0'))) nizi
(* val primer_regex_7 : string list = [""; "0"] *)

(*----------------------------------------------------------------------------*
 Definirajte funkcijo `stik_nfa: NFA.t -> NFA.t -> NFA.t`. Vrnjeni avtomat
 sprejme nize sestavljene iz stika prvega dela, ki ga sprejme avtomat v prvem
 argumentu, in drugega dela, ki ga sprejme avtomat v drugem argumentu.
[*----------------------------------------------------------------------------*)

let stik_nfa avt1 avt2 = 
  (*Dodamo stanja iz prvega avtomata.*)
  let prva_stanja = NFA.seznam_stanj avt1 in
  let rec pisi_stanja j stik =
  if j = List.length prva_stanja then
    stik
  else
    let trenutno1 = List.nth prva_stanja j in
    let nov_stik = NFA.dodaj_stanje trenutno1 false stik in
    pisi_stanja (j+1) nov_stik
  in
  let stik_stanja1 = pisi_stanja 0 (NFA.ustvari (NFA.zacetno_stanje avt1) false )in
  (*Dodamo prehode med stanji prvega avtomata.*)
  let prvi_prehodi = NFA.seznam_prehodov avt1 in
  let rec pisi_prehode i stik =
    if i = List.length prvi_prehodi then
      stik
    else
      match List.nth prvi_prehodi i with
      | (ime1, None, ime2) -> 
        let nov_stik = NFA.dodaj_prazen_prehod ime1 ime2 stik in
        pisi_prehode (i+1) nov_stik
      | (ime1, Some znak, ime2) -> 
        let nov_stik = NFA.dodaj_prehod ime1 znak ime2 stik in
        pisi_prehode (i+1) nov_stik
  in
  let stik_avt1 = pisi_prehode 0 stik_stanja1 in
  (*Iz vsakega sprejemnega stanja prvega avtomata naredimo
  prazen prehod na začetno stanje drugega avtomata*)
  let rec najdi_sprejemna i stik =
    if i = List.length (NFA.seznam_stanj avt1) then
      stik
    else
      let trenutno1 = List.nth (NFA.seznam_stanj avt1) i in
      if NFA.je_sprejemno_stanje avt1 trenutno1 then
        let stik = NFA.dodaj_prazen_prehod trenutno1 (NFA.zacetno_stanje avt2 ^ "c2") stik in
        najdi_sprejemna (i+1) stik
      else
        najdi_sprejemna (i+1) stik
  in
  let stik_zacetno2 = najdi_sprejemna 0 stik_avt1 in
  (*Dodamo stanja iz drugega avtomata.*)
  let druga_stanja = NFA.seznam_stanj avt2 in
  let rec pisi_stanja j stik =
  if j = List.length druga_stanja then
    stik
  else
    let trenutno2 = List.nth druga_stanja j in
    let nov_stik = NFA.dodaj_stanje (trenutno2 ^ "c2") (NFA.je_sprejemno_stanje avt2 trenutno2) stik in
    pisi_stanja (j+1) nov_stik
  in
  let stik_stanja2 = pisi_stanja 0 stik_zacetno2 in
  (*Dodamo prehode med stanji drugega avtomata.*)
  let drugi_prehodi = NFA.seznam_prehodov avt2 in
  let rec pisi_prehode i stik =
    if i = List.length drugi_prehodi then
      stik
    else
      match List.nth drugi_prehodi i with
      | (ime1, None, ime2) -> 
        let nov_stik = NFA.dodaj_prazen_prehod (ime1 ^ "c2") (ime2 ^"c2") stik in
        pisi_prehode (i+1) nov_stik
      | (ime1, Some znak, ime2) -> 
        let nov_stik = NFA.dodaj_prehod (ime1 ^ "c2") znak (ime2 ^"c2") stik in
        pisi_prehode (i+1) nov_stik
  in
  let stik_koncen = pisi_prehode 0 stik_stanja2 in
  stik_koncen



let primer_regex_8 = List.filter (nfa_sprejema (stik_nfa (znak_nfa '0') (znak_nfa '1'))) nizi
(* val primer_regex_8 : string list = ["01"] *)

(*----------------------------------------------------------------------------*
 Definirajte funkcijo `kleenejevo_zaprtje_nfa: NFA.t -> NFA.t`. Vrnjeni avtomat
 naj sprejme nize, ki jih dobimo s poljubnim ponavljanjem nizov, ki jih sprejme
 avtomat v argumentu.
[*----------------------------------------------------------------------------*)

let kleenejevo_zaprtje_nfa avtomat = 
  let star = NFA.ustvari (NFA.zacetno_stanje avtomat) true in
  (*Kopiramo vse iz avtomata, spremenimo le to, da bo začetno stanje sprejemno. 
  Dodamo stanja iz avtomata.*)
  let stanja = NFA.seznam_stanj avtomat in
  let rec pisi_stanja j star =
    if j = List.length stanja then
      star
    else if List.nth stanja j = NFA.zacetno_stanje avtomat then
      pisi_stanja (j+1) star
    else
      let trenutno = List.nth stanja j in
      let nov_star = NFA.dodaj_stanje trenutno (NFA.je_sprejemno_stanje avtomat trenutno) star in
      pisi_stanja (j+1) nov_star
  in
  let star_stanja = pisi_stanja 0 star in
  (*Dodamo prehode med stanji avtomata.*)
  let prehodi = NFA.seznam_prehodov avtomat in
  let rec pisi_prehode i star =
    if i = List.length prehodi then
      star
    else
      match List.nth prehodi i with
      | (ime1, None, ime2) -> 
        let nov_star = NFA.dodaj_prazen_prehod ime1 ime2 star in
        pisi_prehode (i+1) nov_star
      | (ime1, Some znak, ime2) -> 
        let nov_star = NFA.dodaj_prehod ime1 znak ime2 star in
        pisi_prehode (i+1) nov_star
  in
  let star_prehodi = pisi_prehode 0 star_stanja in
  (*Iz vsakega sprejemnega stanja dodamo prazen prehod v začetno stanje.*)
  let rec najdi_sprejemna i avto =
    if i = List.length (NFA.seznam_stanj avto) then
      avto
    else
      let trenutno = List.nth (NFA.seznam_stanj avto) i in
      if NFA.je_sprejemno_stanje avto trenutno then
        let nov_avto = NFA.dodaj_prazen_prehod trenutno (NFA.zacetno_stanje avto) avto in
        najdi_sprejemna (i+1) nov_avto
      else
        najdi_sprejemna (i+1) avto
  in
  najdi_sprejemna 0 star_prehodi


let () = kleenejevo_zaprtje_nfa enke_ali_nicle_deljive_s_3 |> dot_of_nfa |> print_endline
let primer_regex_9 = List.filter (nfa_sprejema (kleenejevo_zaprtje_nfa (znak_nfa '0'))) nizi
(* val primer_regex_9 : string list = [""; "0"; "00"; "000"; "0000"; "00000"] *)

(*----------------------------------------------------------------------------*
 Zgoraj definirane funkcije združite v definicijo funkcije `nfa_of_regex: regex
 -> NFA.t`, ki danemu regularnemu izrazu priredi `NFA`, ki sprejme isti jezik.
[*----------------------------------------------------------------------------*)

let rec nfa_of_regex reg = 
  match reg with
  | Empty -> prazen_nfa
  | Eps -> epsilon_nfa
  | Char znak -> znak_nfa znak
  | Union (r1, r2) -> unija_nfa (nfa_of_regex r1) (nfa_of_regex r2)
  | Concat (r1, r2) -> stik_nfa (nfa_of_regex r1) (nfa_of_regex r2)
  | Star r -> kleenejevo_zaprtje_nfa (nfa_of_regex r)


let primer_regex_10 = List.filter (nfa_sprejema (nfa_of_regex re_enke_deljive_s_3)) nizi
(* val primer_regex_10 : string list =
  [""; "0"; "00"; "000"; "111"; "0000"; "0111"; "1011"; "1101"; "1110";
   "00000"; "00111"; "01011"; "01101"; "01110"; "10011"; "10101"; "10110";
   "11001"; "11010"; "11100"] *)

let primer_regex_11 = List.filter (regex_sprejema re_enke_deljive_s_3) nizi
(* val primer_regex_11 : string list =
  [""; "0"; "00"; "000"; "111"; "0000"; "0111"; "1011"; "1101"; "1110";
   "00000"; "00111"; "01011"; "01101"; "01110"; "10011"; "10101"; "10110";
   "11001"; "11010"; "11100"] *)


