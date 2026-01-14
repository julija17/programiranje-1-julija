-- Datoteka vsebuje primere ekvivalenc na induktivnih tipih. Razdeljena je na več delov glede na strukturo, za katero dokazujemo ekvivalence.

-- 1. Seznami

-- 1.a. Seznam celih števil (List Int) - primer s predavanj
def vsota : List Int → Int
  | .nil => 0
  | .cons x xs => x + vsota xs

def pomozna : List Int → Int → Int :=
  fun xs => fun acc =>
    match xs with
    | .nil => acc
    | .cons x xs => pomozna xs (acc + x)

def vsota' : List Int → Int :=
  fun xs => pomozna xs 0

-- Za lažji dokaz končne ekvivalence vsot najprej dokažemo pomožno lemo,
-- ki utemelji pravilnost pomožne funkcije z akumulatorjem
theorem vsota_pomozna : forall (xs : List Int) (acc : Int),
  acc + vsota xs = pomozna xs acc :=
  by
    intro xs
    induction xs with
    | nil =>
        simp [pomozna, vsota]
    | cons x xs' ih =>
        intro acc
        calc
          acc + vsota (x :: xs')
          _ = acc + (x + vsota xs') := by simp [vsota]
          _ = (acc + x) + vsota xs' := by rw [Int.add_assoc] -- lahko kar `by omega`
          _ = pomozna xs' (acc + x) := by rw [ih]
          _ = pomozna (x :: xs') acc := by simp [pomozna]

theorem vsoti_enaki : ∀ xs : List Int, vsota xs = vsota' xs :=
  by
    sorry

-- 1.b. Seznam poljubnega tipa (List A), ogledamo operacije stika, obračanja in dolžine

-- Definicije operacij
def stakni {A : Type} : List A → List A → List A :=
  fun xs ys =>
    match xs with
    | [] => ys
    | x :: xs' => x :: stakni xs' ys

#eval (stakni ["a", "b"] ["c", "d"])

def obrni {A : Type} : List A → List A :=
  fun xs =>
    match xs with
    | [] => []
    | x :: xs' => stakni (obrni xs') [x]

#eval (obrni ["a", "b", "c", "d"])

def dolzina {A : Type} : List A → Nat :=
  fun xs =>
    match xs with
    | [] => 0
    | _ :: xs' => 1 + dolzina xs'

#eval (dolzina ["a", "b", "c", "d"])

-- Trditve
theorem trd1  {A : Type} {x : A} : obrni [x] = [x] :=
  by
    -- rw [obrni, obrni, stakni]
    simp [obrni, stakni]

-- Trditvi 2 in 3 ste na predavanjih dokazali s pomočjo računanja po korakih `calc`
theorem trd2 {A : Type} {xs ys : List A} : dolzina (stakni xs ys) = dolzina xs + dolzina ys :=
  by
    induction xs with
    | nil => simp [stakni, dolzina]
    | cons x xs ip =>
      simp [stakni, dolzina]
      rw [ip]
      -- simp [Nat.add_assoc]
      omega


theorem trd3 {A : Type} {xs : List A} : stakni xs [] = xs :=
  by
    induction xs with
    | nil => simp [stakni]
    | cons x xs ip =>
      simp [stakni, ip]

theorem trd4 {A : Type} {xs ys zs : List A} : stakni (stakni xs ys) zs = stakni xs (stakni ys zs) :=
  by
    induction xs with
    | nil => simp [stakni]
    | cons x xs ip =>
      simp [stakni]
      rw [ip]

theorem trd5 {A : Type} {xs ys : List A} : obrni (stakni xs ys) = stakni (obrni ys) (obrni xs) :=
  by
    induction xs with
    | nil =>
      simp [stakni, obrni, trd3]
    | cons x xs ip =>
      simp [stakni, obrni, ip, trd4]

theorem trd6 {A : Type} {xs : List A} : dolzina (obrni xs) = dolzina xs :=
  by
    induction xs with
    | nil => simp [obrni, dolzina]
    | cons x xs ip =>
      simp [obrni, dolzina, trd2, ip]
      omega


theorem trd7 {A : Type} {xs : List A} : obrni (obrni xs) = xs :=
  by
    induction xs with
    | nil => simp [obrni]
    | cons x xs ip =>
      simp [obrni]
      rw [← trd1, trd5]
      simp [trd1, ip, stakni]

-- 1.c. Seznam poljubnega tipa (List A), dodamo preslikave

-- Definicija preslikave
def preslikaj {A B : Type} : (A → B) → List A → List B :=
  fun f xs =>
    sorry

-- Trditve
theorem trd8 {A B C : Type} {f : A → B} {g : B → C} {xs : List A} : preslikaj g (preslikaj f xs) = preslikaj (g ∘ f) xs :=
  by
    sorry

theorem trd9 {A : Type} {xs : List A} : preslikaj id xs = xs :=
  by
    sorry

theorem trd10 {A B : Type} {f : A → B} {xs ys : List A} : preslikaj f (stakni xs ys) = stakni (preslikaj f xs) (preslikaj f ys) :=
  by
    sorry

theorem trd11 {A B : Type} {f : A → B} {xs : List A} : preslikaj f (obrni xs) = obrni (preslikaj f xs) :=
  by
    sorry

-- 2. Dvojiška drevesa
inductive tree (A : Type) : Type where
  | empty : tree A
  | node : A → tree A → tree A → tree A

#check tree.rec

-- 2.a. Preslikave na drevesih
def preslikaj_drevo {A B : Type} : (A → B) → tree A → tree B :=
  fun f t =>
    match t with
    | .empty => .empty -- Ne potrebujemo `tree.empty`, ker Lean sam sklepa tip
    | .node x l r => .node (f x) (preslikaj_drevo f l) (preslikaj_drevo f r)

-- Trditvi
theorem trd12 {A B : Type} {f : A → B} : preslikaj_drevo f tree.empty = tree.empty :=
  by
    simp [preslikaj_drevo]

theorem trd13 {A B C : Type} {f : A → B} {g : B → C} {t : tree A} : preslikaj_drevo g (preslikaj_drevo f t) = preslikaj_drevo (g ∘ f) t :=
  by
    induction t with
    | empty =>
      simp [preslikaj_drevo]
    | node x l r ihl ihr =>
      simp [preslikaj_drevo]
      -- exact ⟨ihl, ihr⟩
      constructor -- enako kot apply And.intro
      · exact ihl
      · exact ihr


-- 2.b. Globina drevesa in zrcaljenje drevesa
def globina {A : Type} : tree A → Nat :=
  fun t =>
    match t with
    | .empty => 0
    | .node _ l r => (globina l) + (globina r) + 1


def zrcali {A : Type} : tree A → tree A :=
  fun t =>
    match t with
    | .empty => .empty
    | .node x l r => .node x r l

theorem max_comm {a b : Nat} : Nat.max a b = Nat.max b a := -- To trditev preberemo iz knjižnice
  Nat.max_comm a b

-- Trditvi
theorem trd14 {A : Type} {t : tree A} : globina (zrcali t) = globina t :=
  by
    induction t with
    | empty => simp [zrcali, globina]
    | node x l r hl hr => simp [zrcali, globina, Nat.add_comm]

theorem trd15 {A : Type} {t : tree A} : zrcali (zrcali t) = t :=
  by
    induction t with
    | empty => simp [zrcali]
    | node x l r hl hr => simp [zrcali]

-- 2.c. Zbiranje elementov drevesa
def zberi {A : Type} : tree A → List A :=
  fun t =>
    match t with
    | .empty => []
    | .node x l r => x :: (stakni (zberi l) (zberi r))

-- Trditvi
theorem trd16 {A : Type} {y : A} {xs ys : List A} : stakni xs (y::ys) = stakni (stakni xs [y]) ys :=
  by
    sorry

theorem trd17 {A : Type} {t : tree A} : zberi (zrcali t) = obrni (zberi t) :=
  by
    sorry

-- 2.d. Število elementov drevesa
def velikost {A : Type} : tree A → Nat :=
  fun t =>
    sorry

theorem trd18 {A : Type} {t : tree A} : velikost (zrcali t) = velikost t :=
  by
    sorry

-- 3. Indukcija na pomožnih funkcijah z akumulatorjem - Seznami

-- Definirajte repno rekurzivno funkcijo, ki obrne seznam
def obrni' {A : Type} : List A → List A :=
  fun xs =>
    let rec aux (sez : List A) (acc : List A) : List A :=
      match sez with
      | [] => acc
      | x :: sez' => aux sez' (x :: acc)
    aux xs []

-- Dokažite, da je vaša funkcija pravilna
theorem lema_aux {A : Type} : ∀ {xs acc : List A}, obrni'.aux xs acc = stakni (obrni xs) acc :=
  by
    intro xs acc
    induction xs generalizing acc with
    | nil =>
      simp [obrni, stakni, obrni'.aux]
    | cons x xs ip =>
      simp [obrni'.aux, obrni, ip, trd4, stakni]

theorem obrni_enako_obrni' {A : Type} : ∀ {xs : List A}, obrni xs = obrni' xs :=
  by
    intro xs
    calc
      obrni xs
      _ = stakni (obrni xs) [] := by rw [trd3]
      _ = obrni'.aux xs [] := by rw [lema_aux]
      _ = obrni' xs := by simp [obrni']
