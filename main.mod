set UJECIE_WODY;

# Zakresy wolumenu produkcji ujec o roznych kosztach
set ZAKRESY ordered;

####################################################

# Liczba godziny w których trzeba podjąc decyzje co do pracy ujęc
param G >= 1;

# Maksymalna wydajnoœc ujec wody [t/h]
param maksymalnaProdukcja {UJECIE_WODY} >= 0;

# Koszta zmienne pracy ujec [zl/t] 
param kosztZmienny {UJECIE_WODY, ZAKRESY} >= 0;

# Progi zakresow wolumenu produkcji o roznych kosztach [t/h]
param progiZakresowProdukcji {UJECIE_WODY, ZAKRESY} >= 0;

# Koszta stale pracy ujec [zl/h]
param kosztStaly {UJECIE_WODY} >= 0;

# Iloœc wytwarzanych zanieczyszczeñ [g/t]
param zanieczyszczenie {UJECIE_WODY} >= 0;

# Zapotrzebowanie na wode w kolejnych godzinach [t]
param zapotrzebowanieGodzinowe {1..G} >= 0;

####################################################

# Aktywnoœc danego ujecia w danej godzinie
var aktywne {1..G, UJECIE_WODY} binary;

# Wolumen produkcji wody danego ujecia w danej godzinie
var produkcjaWody {1..G, i in UJECIE_WODY} >=0, <= maksymalnaProdukcja[i];

# Godzinowa produkcja
var produkcjaGodzinowa {1..G} >= 0;

# Wolumen produkcji wody przypadajacy na dany zakres kosztow dla danego ujecia w danej godzinie
var produkcjaWodyWPrzedziale {1..G, i in UJECIE_WODY, r in ZAKRESY} >=0; 
var rozpoczetoWysokiZakresProdukcjiWody {t in 1..G, i in UJECIE_WODY, r in ZAKRESY} binary;

# Koszt zmienny poboru wody przez dane ujecie w danej godzinie
var kosztZmiennyUjecia {1..G, UJECIE_WODY} >= 0; 

# Koszta stale pracy ujec dla danej godziny
var kosztStalyUjecia {1..G} >= 0;

# Koszta zmienne pracy ujec w danej godzinie
var godzinowyKosztZmienny {1..G} >= 0;

# Koszt pracy ujec dla danej godziny
var godzinowyKosztCalkowity {1..G} >= 0;

# Calkowity koszt pracy ujec wody
var kosztCalkowity >= 0;

# Calkowita iloœc wytwarzanych zanieczyszczeñ przy zalozonym wolumenie produkcji
var zanieczyszczenieCalkowite >= 0;

####################################################
 
# Obliczenie godzinowej produkcji
subject to ObliczGodzinowaProdukcja {t in 1..G}:
	produkcjaGodzinowa[t] = sum {i in UJECIE_WODY} produkcjaWody[t,i];

# Ograniczenia zakresow kosztow produkcji
subject to Zakres_ograniczenie_1 {t in 1..G, i in UJECIE_WODY}:
	produkcjaWodyWPrzedziale[t,i,first(ZAKRESY)] <= progiZakresowProdukcji[i,first(ZAKRESY)];
subject to Zakres_ograniczenie_2 {t in 1..G, i in UJECIE_WODY, r in ZAKRESY: r != first(ZAKRESY)}:
	produkcjaWodyWPrzedziale[t,i,r] <= (progiZakresowProdukcji[i,r]-progiZakresowProdukcji[i,prev(r)]) * rozpoczetoWysokiZakresProdukcjiWody[t,i,prev(r)];
subject to Zakres_ograniczenie_3 {t in 1..G, i in UJECIE_WODY}:
	progiZakresowProdukcji[i,first(ZAKRESY)]*rozpoczetoWysokiZakresProdukcjiWody[t,i,first(ZAKRESY)] <= produkcjaWodyWPrzedziale[t,i,first(ZAKRESY)];
subject to Zakres_ograniczenie_4 {t in 1..G, i in UJECIE_WODY, r in ZAKRESY: r != first(ZAKRESY)}:
	(progiZakresowProdukcji[i,r]-progiZakresowProdukcji[i,prev(r)])*rozpoczetoWysokiZakresProdukcjiWody[t,i,r] <= produkcjaWodyWPrzedziale[t,i,r];

# Obliczenie wolumenu produkcji dla danego ujecia
subject to ObliczProdukcjeUjecia {t in 1..G, i in UJECIE_WODY}:
	produkcjaWody [t,i] = sum {r in ZAKRESY} produkcjaWodyWPrzedziale[t,i,r];

# Obliczenie kosztow pracy ujec
subject to ObliczGodzinowyKosztStaly {t in 1..G}:
	kosztStalyUjecia[t] = sum {i in UJECIE_WODY} kosztStaly[i] * aktywne[t,i];
subject to ObliczKosztZmiennyUjecia {t in 1..G, i in UJECIE_WODY}:
	kosztZmiennyUjecia[t,i] = sum {r in ZAKRESY} produkcjaWodyWPrzedziale[t,i,r]*kosztZmienny[i,r];
subject to ObliczGodzinowyKosztZmienny {t in 1..G}:
	godzinowyKosztZmienny[t] = sum {i in UJECIE_WODY} kosztZmiennyUjecia[t,i];
subject to ObliczGodzinowyKoszt {t in 1..G}:
	godzinowyKosztCalkowity[t] = kosztStalyUjecia[t] + godzinowyKosztZmienny[t];
subject to ObliczKosztCalkowity:
	kosztCalkowity = sum {t in 1..G} godzinowyKosztCalkowity[t];

# Obliczenie calkowitej ilosci wyprodukowanych zanieczyszczeñ
subject to ObliczZanieczyszczenieCalkowite:
	zanieczyszczenieCalkowite = sum {t in 1..G, i in UJECIE_WODY} produkcjaWody[t,i] * zanieczyszczenie[i];

# Ograniczenia na zapewnienie aktywnosci co najmniej dwoch ujec w kazdej godzinie
subject to MinimalnaLiczbaAktywnychUjec {t in 1..G}:
	sum {i in UJECIE_WODY} aktywne[t,i] >= 2;

# Ograniczenia na pokrycie zapotrzebowania na wode w kazdej godzinie
subject to GodzinoweZapotrzebowanie {t in 1..G}:
	produkcjaGodzinowa[t] = zapotrzebowanieGodzinowe[t];

# Ograniczenia na wolumen planowanej produkcji aktywnych ujec
subject to BrakProdukcjiWodyWWylaczonychUjeciach {t in 1..G, i in UJECIE_WODY}:
	aktywne[t,i] = 0 ==> produkcjaWody[t,i] = 0;

####################################################

# Skladniki wektora oceny
set RATED = {"COST", "POLLUT"};

# Wektor oceny
var value {r in RATED} = 
	if r == "COST" then kosztCalkowity
 	else if r == "POLLUT" then zanieczyszczenieCalkowite;

# Wektor aspiracji
param aspiration {RATED};

# Wspolczynniki normalizujace - ujemna lambda gdy minimalizujemy skladnik
param lambda {RATED};

# Wspolczynnik skladnika regularyzacyjnego
param epsilon;

# Wspolczynnik pomniejszenia wartoœci ocen ponad poziomem aspiracji
param beta;

# Indywidualne funkcje osiagniec
var ocenyIndywidualne {RATED};

# Zmienna pomocnicza metody punktu odniesienia
var v;

# Skalaryzujaca funkcja osiagniecia
var rating = v + epsilon * (sum {r in RATED} ocenyIndywidualne[r]);

# Odlegloœc od punktu odniesienia
var distance {r in RATED} = value[r]-aspiration[r];

# Znormalizowana odlegloœc od punktu odniesienia
var normalizedDistance {r in RATED} = lambda[r]*distance[r];


# Ograniczenia zmiennej v przez indywidualne funkcje osiagniec
subject to VSubject {r in RATED}:
	v <= ocenyIndywidualne[r]; 

# Ograniczenia indywidualnych funkcji osiagniec
subject to IndividualRatingSubjectBeta {r in RATED}:
	ocenyIndywidualne[r] <= beta*normalizedDistance[r];
subject to IndividualRatingSubject {r in RATED}:
	ocenyIndywidualne[r] <= normalizedDistance[r];
	
####################################################
minimize MinimizeCost: kosztCalkowity;
minimize MinimizePollution: zanieczyszczenieCalkowite;

maximize MaximizeCost: kosztCalkowity;
maximize MaximizePollution: zanieczyszczenieCalkowite

maximize MaximizeRating: rating;

