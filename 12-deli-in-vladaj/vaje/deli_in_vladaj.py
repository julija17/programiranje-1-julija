###############################################################################
# Če imamo dve urejeni tabeli, potem urejeno združeno tabelo dobimo tako, da
# urejeni tabeli zlijemo. Pri zlivanju vsakič vzamemo manjšega od začetnih
# elementov obeh tabel. Zaradi učinkovitosti ne ustvarjamo nove tabele, ampak
# rezultat zapisujemo v že pripravljeno tabelo (ustrezne dolžine).
#
# Funkcija naj deluje v času O(n), kjer je n dolžina tarčne tabele.
#
# Sestavite funkcijo [merge(target, list_1, list_2)], ki v tabelo [target]
# zlije tabeli [list_1] in [list_2]. V primeru, da sta elementa v obeh tabelah
# enaka, naj bo prvi element iz prve tabele.
#
# Primer:
#
#     >>> list_1 = [1, 3, 5, 7, 10]
#     >>> list_2 = [1, 2, 3, 4, 5, 6, 7]
#     >>> target = [-1 for _ in range(len(list_1) + len(list_2))]
#     >>> merge(target, list_1, list_2)
#     >>> target
#     [1, 1, 2, 3, 3, 4, 5, 5, 6, 7, 7, 10]
#
###############################################################################

#def merge(target, list_1, list_2) :
#    for i in range(0, len(target)) :
#        if list_1[0] <= list_2[0] :
#            target[i] = list_1[0]
#            list_1 = list_1[1:]
#        elif list_1[0] > list_2[0] or list_1 == []:
#            target[i] = list_2[0]
#            list_2 = list_2[1:]
#    return None
    
def merge(target, list1, list2) :
    i1 = 0
    i2 = 0
    while i1 < len(list1) and i2 < len(list2) :
        if list1[i1] <= list2[i2] :
            target[i1 + i2] = list1[i1]
            i1 += 1
        else:
            target[i1 + i2] = list2[i2]
            i2 += 1
    while i1 < len(list1) :
        target[i1 + i2] = list1[i1]
        i1 += 1
    while i2 < len(list2) :
        target[i1 + i2] = list1[i2]
        i2 += 1
    

###############################################################################
# Tabelo želimo urediti z zlivanjem (merge sort). Tabelo razdelimo na polovici,
# ju rekurzivno uredimo in nato zlijemo z uporabo funkcije [zlij].
#
# Namig: prazna tabela in tabela z enim samim elementom sta vedno urejeni.
#
# Napišite funkcijo [mergesort(a)], ki uredi tabelo [a] s pomočjo zlivanja. Za
# razliko od hitrega urejanja tu tabele lahko kopirate, zlivanje pa je potrebno
# narediti na mestu.
#
#     >>> a = [10, 4, 5, 15, 11, 3, 17, 2, 18]
#     >>> mergesort(a)
#     >>> a
#     [2, 3, 4, 5, 10, 11, 15, 17, 18]
###############################################################################



###############################################################################
# Na predavanjih ste implementirali imperativno verzijo pivotiranja v OCamlu, 
# prepišite jo v Python in jo uporabite kot osnovo za reševanje problemov s 
# pomočjo metode deli in vladaj.
# 
# Želimo definirati pivotiranje na mestu za tabelo [a]. Ker bi želeli
# pivotirati zgolj dele tabele, se omejimo na del tabele, ki se nahaja med
# indeksoma [start] in [end] (vključujoč oba robova).
#
# Primer: za [start = 1] in [end = 7] tabelo
#
#     [10, 4, 5, 15, 11, 2, 17, 0, 18]
#
# preuredimo v
#
#     [10, 0, 2, 4, 11, 5, 17, 15, 18]
#
# (Možnih je več različnih rešitev, pomembno je, da je element 4 pivot.)
#
# Sestavi funkcijo [pivot(a, start, end)], ki preuredi tabelo [a] tako, da bo
# element [ a[start] ] postal pivot za del tabele med indeksoma [start] in
# [end]. Funkcija naj vrne indeks, na katerem je po preurejanju pristal pivot.
# Funkcija naj deluje v času O(n), kjer je n dolžina tabele [a].
#
# Primer:
#
#     >>> a = [10, 4, 5, 15, 11, 2, 17, 0, 18]
#     >>> pivot(a, 1, 7)
#     3
#     >>> a
#     [10, 0, 2, 4, 11, 5, 17, 15, 18]
###############################################################################



###############################################################################
# V tabeli želimo poiskati vrednost k-tega elementa po velikosti.
#
# Primer: Če je
#
#     >>> a = [10, 4, 5, 15, 11, 3, 17, 2, 18]
#
# potem je tretji element po velikosti enak 5, ker so od njega manši elementi
#  2, 3 in 4. Pri tem štejemo indekse od 0 naprej, torej je "ničti" element 2.
#
# Sestavite funkcijo [kth_element(a, k)], ki v tabeli [a] poišče [k]-ti element
# po velikosti. Funkcija sme spremeniti tabele [a]. Cilj naloge je, da jo
# rešite brez da v celoti uredite tabelo [a].
###############################################################################



###############################################################################
# Tabelo a želimo urediti z algoritmom hitrega urejanja (quicksort).
#
# Napišite funkcijo [quicksort(a)], ki uredi tabelo [a] s pomočjo pivotiranja.
# Poskrbi, da algoritem deluje 'na mestu', torej ne uporablja novih tabel.
#
# Namig: Definirajte pomožno funkcijo [quicksort_part(a, start, end)], ki
#        uredi zgolj del tabele [a].
#
#     >>> a = [10, 4, 5, 15, 11, 3, 17, 2, 18]
#     >>> quicksort(a)
#     >>> a
#     [2, 3, 4, 5, 10, 11, 15, 17, 18]
###############################################################################

def quicksort_part(a, start, end):
    pindex = start
    pivot = a[pindex]
    desno = start + 1
    while desno < end:
        if desno >= pivot:
            desno += 1
        else:
            zadnji = a[desno]
            naslednjik = a[pindex + 1]
            a[pindex] = zadnji
            a[pindex + 1] = pivot
            a[desno] = naslednjik
            desno += 1  
            pindex += 1


def pivot(a, start, end):
    ind_pivota = start
    naslednji = start + 1
    while naslednji < end + 1:
        if a[naslednji] < a[ind_pivota]:
            pivot = a[int_pivota]
            a[ind_pivota] = a[naslednji]
            a[naslednji] = a[ind_pivota + 1]
            a[ind_pivota + 1] = pivot
            ind_pivota += 1
        naslednji += 1
    return ind_pivota


def quicksort(a):
    return None