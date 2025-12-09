-- Propoziční extenzionalita - dva ekvivalentní výroky jsou si rovny
axiom propext' {a b : Prop} : (a ↔ b) → a = b
-- Axiom výběru - z neprázdné množiny si vyberu prvek
axiom choice' {α : Sort u} : Nonempty α → α
-- Typová konstrukce - tvoří nové typy - podobné třídám ekvivalence - zatím prázdné ale
axiom Quot' : {α : Sort u} → (α → α → Prop) → Sort u
-- Vkládá prvky do daného typu - třídy ekvicalence
axiom Quot.mk' : {α : Sort u} → (r : α → α → Prop) → α → Quot' r
-- Princip indukce pro kvocienty - chci-li ukázat nějakou vlastnost β platí pro každý prvek,
-- stačí ukázat, že platí pro každý původní prvek
axiom Quot.ind' :
    ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
      (∀ a, β (Quot.mk r a)) → (q : Quot r) → β q
-- Jak definovat funkci ven z typu
axiom Quot.lift' :
    {α : Sort u} → {r : α → α → Prop} → {β : Sort u} → (f : α → β)
    → (∀ a b, r a b → f a = f b) → Quot r → β
-- Je-li relace mezi dvěma prvky, tak se jejich typy rovnají - jsou ve stejné třídě ekvivalence
axiom Quot.sound' :
    ∀ {α : Type u} {r : α → α → Prop} {a b : α},
      r a b → Quot.mk' r a = Quot.mk' r b
