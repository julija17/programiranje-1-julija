set_option autoImplicit false

/------------------------------------------------------------------------------
 ## Naravna števila

 - Definirajte funkcijo, ki *rekurzivno* (torej naivno in ne direktno s formulo,
    ki jo boste morali dokazati) sešteje prvih `n` lihih naravnih števil, ter
    dokažite, da zanjo velja znana enakost.
 - Definirajte funkcijo, ki *rekurzivno* sešteje prvih `n` produktov dveh
    zaporednih naravnih števil, ter dokažite da zanjo velja znana enakost
    (najprej v obliki, ki ne zahteva deljenja, nato pa še v običajni obliki).

 Indukcijska koraka dokazov trditev `vsota_lihih_kvadrat` in `formula_produktov`
 dokažite z uporabo `calc` bloka.

 *Namig*: pri krajših manipulacijah numeričnih literalov nam taktika `rfl`
 pogosto zadostuje.
------------------------------------------------------------------------------/

-- Vsota prvih n lihih naravnih števil
def vsota_lihih : Nat → Nat :=
  fun n =>
    match n with
    | Nat.zero => 0
    | Nat.succ n' => 2 * n' + 1 + vsota_lihih n'

theorem vsota_lihih_kvadrat : (n : Nat) → vsota_lihih n = n * n :=
  by
    intro n
    induction n with
    | zero =>
      rw[Nat.mul_zero]
      rfl
    | succ n' ip =>
      calc
        vsota_lihih (n' + 1)
        _ = 2 * n' + 1 + vsota_lihih n' := by rw [vsota_lihih]
        _ = 2 * n' + 1 + n' * n' := by rw [ip]
        _ = ((n' + n') + 1) + n' * n' := by rw [Nat.two_mul]
        _ = n' * n' + ((n' + n') + 1) := by simp [Nat.add_comm, Nat.add_assoc]
        _ = n' * n' + n' + n' + 1 := by simp [Nat.add_assoc]
        _ = (n' + 1) * (n' + 1) := by rw [Nat.add_one_mul_add_one]

-- Vsota prvih n produktov zaporednih naravnih števil
def vsota_produktov : Nat → Nat :=
  fun n =>
    match n with
    | Nat.zero => 0
    | Nat.succ n' => n * (n + 1) + vsota_produktov n'


theorem formula_produktov : (n : Nat) → 3 * vsota_produktov n = n * (n + 1) * (n + 2) :=
  by
    intro n
    induction n with
    | zero =>
      rw [vsota_produktov, Nat.mul_zero]
    | succ n' ip =>
      calc
        3 * vsota_produktov (n' + 1)
        _ = 3 * ((n' + 1) * (n' + 1 + 1) + vsota_produktov n') := by rw [vsota_produktov, Nat.succ_eq_add_one]
        _ = 3 * (n' + 1) * (n' + 1 + 1) + 3 * vsota_produktov n' := by rw [Nat.mul_add, Nat.mul_assoc]
        _ = 3 * (n' + 1) * (n' + 1 + 1) + n' * (n' + 1) * (n' + 2) := by rw [ip]
        _ = (n' + 1) * 3 * (n' + 1 + 1) + (n' + 1) * n' * (n' + 2) := by simp [Nat.mul_comm]
        _ = (n' + 1) * (3 * (n' + 1 + 1)) + (n' + 1) * (n' * (n' + 2)) := by simp [Nat.mul_assoc]
        _ = (n' + 1) * ((1 + 2) * (n' + 1 + 1) + n' * (n' + 2)) := by simp [Nat.mul_add]
        _ = (n' + 1) * ((1 + 2 + n') * (n' + 1 + 1)) := by simp [Nat.add_mul]
        _ = (n' + 1) * (n' + 1 + 1) * (n' + 1 + 2) := by simp [Nat.add_comm, Nat.mul_comm, Nat.mul_assoc]


theorem prava_formula_produktov : (n : Nat) → vsota_produktov n = (n * (n + 1) * (n + 2)) / 3 :=
  by
    intro n
    calc
      vsota_produktov n
      _ = 3 * (vsota_produktov n) / 3 := by rw [Nat.mul_div_right (vsota_produktov n) (by decide)]
      _ = n * (n + 1) * (n + 2) / 3 := by rw [formula_produktov]

/------------------------------------------------------------------------------
 ## Vektorji

 Definirajmo vektorje z elementi poljubnega tipa. Za ustrezno delovanje
 zapišemo funkcijo stikanja dveh vektorjev s pomočjo taktik.

 Zapišite še funkcije:
 - `obrni`, ki vrne na vektor z elementi v obratnem vrstnem redu,
 - `preslikaj`, ki preslika vse elemente vektorja z dano funkcijo,
 - `zip`, ki združi dva vektorja v vektor parov,
 - `dolzina`, ki vrne dolžino vektorja,
 - `glava` in `rep`, ki varno vrneta glavo in rep *nepraznega* vektorja.
 Rezultati operacij na testnem vektorju `[1,2,3]` so zapisani ob koncu
 razdelka `Vektorji`.

 Dokažite tudi trditve o teh funkcijah:
 - `preslikaj_identiteto`: preslikava elementov vektorja z identiteto pusti
    vektor nespremenjen,
 - `preslikaj_kompozitum`: preslikava s kompozitumom funkcij je enaka
    kompozitumu preslikav s posameznimi funkcijami,
 - `dolzina_pravilna`: dolžina vektorja je enaka njegovi indeksirani dolžini,
 - `preslikaj_in_zip_se_ujemata`: preslikava elementov vektorja in nato
    združevanje z `zip` je enako združevanju z `zip` in nato preslikavi parov.
------------------------------------------------------------------------------/

inductive Vektor : Type → Nat → Type where
  | prazen : {A : Type} → Vektor A 0
  | sestavljen : {A : Type} → {n : Nat} → A → Vektor A n → Vektor A (n + 1)
deriving Repr

def stakni : {A : Type} → {m n : Nat} → Vektor A m → Vektor A n → Vektor A (m + n) :=
  fun xs ys => match xs with
  | .prazen =>
    by
      rw [Nat.add_comm]
      exact ys
  | .sestavljen x xs' =>
    by
      rw [Nat.add_right_comm]
      exact .sestavljen x (stakni xs' ys)

def obrni : {A : Type} → {m : Nat} → Vektor A m → Vektor A m :=
  fun xs => match xs with
  | .prazen => .prazen
  | .sestavljen x xs' =>
    stakni (obrni xs') (.sestavljen x .prazen)


def preslikaj : {A B : Type} → {n : Nat} → (A → B) → Vektor A n → Vektor B n :=
  fun f xs => match xs with
  | .prazen => .prazen
  | .sestavljen x xs' =>
    .sestavljen (f x) (preslikaj f xs')


def zip : {A B : Type} → {n : Nat} → Vektor A n → Vektor B n → Vektor (A × B) n :=
  fun xs ys =>
    match (xs, ys) with
    | (.prazen, .prazen) => .prazen
    | (.sestavljen x xs', .sestavljen y ys') =>
      .sestavljen (x, y) (zip xs' ys')


def dolzina : {A : Type} → {n : Nat} → Vektor A n → Nat :=
  fun xs => match xs with
    | .prazen => 0
    | .sestavljen _ xs' => 1 + (dolzina xs')


def glava : {A : Type} → {n : Nat} → Vektor A (Nat.succ n) → A :=
  fun (.sestavljen x _) => x

def rep : {A : Type} → {n : Nat} → Vektor A (Nat.succ n) → Vektor A n :=
  fun (.sestavljen _ xs) => xs


theorem preslikaj_identiteto : {A : Type} → {n : Nat} → (xs : Vektor A n) →
  preslikaj id xs = xs :=
  by
    intro A n xs
    induction xs with
    | prazen => rw [preslikaj]
    | sestavljen x xs' ip => rw [preslikaj, id, ip]


theorem preslikaj_kompozitum :
  {A B C : Type} → {n : Nat} → (f : A → B) → (g : B → C) → (xs : Vektor A n) →
  preslikaj (fun x => g (f x)) xs = preslikaj g (preslikaj f xs) :=
  by
    intro A B C n f g xs
    induction xs with
    | prazen => simp [preslikaj]
    | sestavljen x xs' ip => simp [preslikaj, ip]


theorem dolzina_pravilna : {A : Type} → {n : Nat} → (xs : Vektor A n) →
  dolzina xs = n :=
  by
    intro A n xs
    induction xs with
    | prazen => rw [dolzina]
    | sestavljen x xs' ip => rw [dolzina, ip, Nat.add_comm]


theorem preslikaj_in_zip_se_ujemata : {A B C : Type} → {n : Nat} →
  (f : A → B) → (g : A → C) → (xs : Vektor A n) →
  zip (preslikaj f xs) (preslikaj g xs) = preslikaj (fun x => (f x, g x)) xs :=
  by
    intro A B C n f g xs
    induction xs with
    | prazen =>
      simp [preslikaj]
      rfl
    | sestavljen x xs' ip =>
      simp [preslikaj]
      calc
        zip (preslikaj f (Vektor.sestavljen x xs')) (preslikaj g (Vektor.sestavljen x xs'))
        _ = zip (Vektor.sestavljen (f x) (preslikaj f xs')) (Vektor.sestavljen (g x) (preslikaj g xs')) := by simp [preslikaj]
        _ = Vektor.sestavljen (f x, g x) (zip (preslikaj f xs') (preslikaj g xs')) := by rfl
        _ = Vektor.sestavljen (f x, g x) (preslikaj (fun x => (f x, g x)) xs') := by rw [ip]


-- Primeri rezultatov operacij
def primer_vektorja : Vektor Nat 3 :=
  .sestavljen 1 (.sestavljen 2 (.sestavljen 3 .prazen))

#eval obrni primer_vektorja
-- Vrne: Vektor.sestavljen 3 (Vektor.sestavljen 2 (Vektor.sestavljen 1 (Vektor.prazen)))
#eval preslikaj (fun x => x + 10) primer_vektorja
-- Vrne: Vektor.sestavljen 11 (Vektor.sestavljen 12 (Vektor.sestavljen 13 (Vektor.prazen)))
#eval zip primer_vektorja primer_vektorja
-- Vrne: Vektor.sestavljen (1, 1) (Vektor.sestavljen (2, 2) (Vektor.sestavljen (3, 3) (Vektor.prazen)))
#eval dolzina primer_vektorja
-- Vrne: 3
#eval glava primer_vektorja
-- Vrne: 1
#eval rep primer_vektorja
-- Vrne: Vektor.sestavljen 2 (Vektor.sestavljen 3 (Vektor.prazen))

/------------------------------------------------------------------------------
 ## Logične izjave in predikatni račun

 Dokažite spodnje logične trditve.

 Dokazati morate 3 izjave brez predikatov in 3 izjave s predikatoma `forall`
 in `exists`. Zadnja je _paradoks pivca_, ki pravi:
   "V vsaki neprazni gostilni obstaja gost, za katerega velja,
   da če pije on, pijejo vsi v gostilni."

 Pri nekaterih dokazih boste potrebovali dokaze klasične logike iz modula
 `Classical`.
------------------------------------------------------------------------------/

theorem dvojna_negacija {P : Prop} : ¬¬P ↔ P :=
  by
    apply Iff.intro
    · intro h
      apply Classical.byContradiction
      intro k
      contradiction
    · intro h
      intro k
      contradiction


theorem trojna_negacija {P : Prop} : ¬¬¬P ↔ ¬P :=
  by
    apply Iff.intro
    · intro h1 h2
      apply h1
      intro h3
      apply h3
      exact h2
    · intro h1 h2
      apply h2
      exact h1


theorem kontrapozitivna_oblika {P Q : Prop} : (P → Q) ↔ (¬Q → ¬P) :=
  by
    apply Iff.intro
    · intro h1 h2 h3
      apply h2
      exact h1 h3
    · intro h1 h2
      apply Classical.byContradiction
      intro h3
      have h4 : ¬P := h1 h3
      contradiction


theorem pravilo_obstaja_disjunkcija : {A : Type} → {P Q : A → Prop} →
  (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) :=
  by
    intro A P Q
    apply Iff.intro
    · intro h1
      obtain ⟨x, h2⟩ := h1
      cases h2 with
      | inl hpx =>
        apply Or.inl
        exact ⟨x, hpx⟩
      | inr hqx =>
        apply Or.inr
        exact ⟨x, hqx⟩
    · intro h1
      cases h1 with
      | inl hpx =>
        obtain ⟨x, h2⟩ := hpx
        exact ⟨x, Or.inl h2⟩
      | inr hqx =>
        obtain ⟨x, h2⟩ := hqx
        exact ⟨x, Or.inr h2⟩


theorem obstaja_p_ali_za_vse_ne_p {A : Type} {P : A → Prop} :
  (∃ x, P x) ∨ (∀ x, ¬ P x) :=
  by
    have h := Classical.em (∃ x, P x)
    cases h with
    | inl hx =>
      left
      exact hx
    | inr hnotx =>
      right
      intro x hpx
      apply hnotx
      exact ⟨x, hpx⟩


theorem paradoks_pivca :
  {G : Type} → {P : G → Prop} →
  (g : G) →  -- (g : G) pove, da je v gostilni vsaj en gost
  ∃ (p : G), (P p → ∀ (x : G), P x) :=
  by
    intro G P p
    have h : (∀ (p : G), P p) ∨ (∃ p, ¬P p):=
      Classical.forall_or_exists_not (P := P)
    cases h with
    | inl hvsipijejo =>
      have imp : P p -> ∀ (x : G), P x := fun _ => hvsipijejo
      exact ⟨p, imp⟩
    | inr hennepije =>
      obtain ⟨p, h2⟩ := hennepije
      have imp : P p -> ∀ (x : G), P x :=
      by
        intro hpp
        contradiction
      exact ⟨p, imp⟩



/------------------------------------------------------------------------------
 ## Dvojiška drevesa

  Podan je tip dvojiških dreves skupaj s funkcijami za zrcaljenje drevesa,
  izračun višine in velikosti drevesa.
  Dokažite trditvi:
 - `zrcaljenje_ohrani_visino`: zrcaljenje drevesa ohrani njegovo višino,
 - `visina_manjsa_ali_enaka_velikosti`: višina drevesa je vedno manjša ali
    enaka njegovi velikosti.

  V drugem delu sta definirani funkciji `vsota` in `vsota'`, ki izračunata
  vsoto vseh elementov v drevesu z naravnimi števili. Prva jo izračuna naivno,
  druga pa z uporabo pomožne funkcije z akumulatorjem. Dokažite, da obe funkciji
  dajeta enak rezultat za vsako drevo z naravnimi števili.
  Do pomožne funkcije `aux` lahko dostopate kot `vsota'.aux`.
-------------------------------------------------------------------------------/

inductive Drevo : Type → Type where
  | prazno : {A : Type} → Drevo A
  | sestavljeno : {A : Type} → A → Drevo A → Drevo A → Drevo A

def visina : {A : Type} → Drevo A → Nat :=
  fun t => match t with
  | .prazno => 0
  | .sestavljeno _ l d => 1 + max (visina l) (visina d)

def zrcali : {A : Type} → Drevo A → Drevo A :=
  fun t => match t with
  | .prazno => .prazno
  | .sestavljeno x l d => .sestavljeno x (zrcali d) (zrcali l)

def velikost : {A : Type} → Drevo A → Nat :=
  fun t => match t with
  | .prazno => 0
  | .sestavljeno _ l d => 1 + velikost l + velikost d

theorem zrcaljenje_ohrani_visino :
  {A : Type} → (t : Drevo A) →
  visina (zrcali t) = visina t :=
  by
    intro A t
    induction t with
    | prazno =>
      rw [zrcali]
    | sestavljeno a l d hl hd =>
      simp [zrcali, visina, hl, hd]
      omega


theorem visina_manjsa_ali_enaka_velikosti :
  {A : Type} → (t : Drevo A) →
  visina t ≤ velikost t :=
  by
    intro A t
    induction t with
    | prazno =>
      rw [visina, velikost]
      omega
    | sestavljeno a l d hl hd =>
      rw [visina, velikost]
      omega


-- Drugi del
def vsota : Drevo Nat → Nat :=
  fun t => match t with
  | .prazno => 0
  | .sestavljeno x l d => x + vsota l + vsota d

def vsota' : Drevo Nat → Nat :=
  let rec aux : Drevo Nat → Nat → Nat :=
    fun t acc => match t with
    | .prazno => acc
    | .sestavljeno x l d => aux l (x + aux d acc)
  fun t => aux t 0



theorem lema_acc {t : Drevo Nat} {acc : Nat} : vsota'.aux t acc = acc + vsota'.aux t 0 :=
  by
    induction t generalizing acc with
    | prazno =>
      simp [vsota'.aux]
    | sestavljeno a l d hl hd =>
      simp [vsota'.aux]
      calc
        vsota'.aux l (a + vsota'.aux d acc)
        _ = a + vsota'.aux d acc + vsota'.aux l 0 := by rw [hl]
        _ = (a + (acc + vsota'.aux d 0)) + vsota'.aux l 0 := by rw [hd]
        _ = ((acc + a) + vsota'.aux d 0) + vsota'.aux l 0 := by simp [Nat.add_assoc, Nat.add_comm]
        _ = acc + (a + vsota'.aux d 0 + vsota'.aux l 0) := by simp [Nat.add_assoc]
        _ = acc + vsota'.aux l (a + vsota'.aux d 0) := by rw [← hl]


theorem vsota_eq_vsota' : ∀ {t : Drevo Nat}, vsota t = vsota' t :=
  by
    intro t
    induction t with
    | prazno =>
      rw [vsota, vsota', vsota'.aux]
    | sestavljeno a l d hl hd =>
      rw [vsota, hl, hd]
      simp [vsota', vsota'.aux]
      calc
        a + vsota'.aux l 0 + vsota'.aux d 0
        _ = a + (vsota'.aux d 0 + vsota'.aux l 0) := by simp [Nat.add_assoc, Nat.add_comm]
        _ = (a + vsota'.aux d 0) + vsota'.aux l 0 := by simp [Nat.add_assoc]
        _ = vsota'.aux l (a + vsota'.aux d 0) := by rw [← lema_acc]
