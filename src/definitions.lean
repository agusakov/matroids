import data.finset

universes u

open finset

variables {α : Type u} [decidable_eq α] -- need decidability for set difference

def independent (ℐ : finset (finset α)) (I₁ I₂ : finset α) (h₁ : I₁ ∈ ℐ) (h₂ : I₂ ∈ ℐ) : Prop := 
  finset.card I₁ < finset.card I₂ → ∃ (e ∈ I₂ \ I₁), (insert e I₁ ∈ ℐ)
-- how should i define this?

def independent' (ℐ : finset α → Prop) : Prop := 
∀ I₁ I₂, ℐ I₁ ∧ ℐ I₂ → finset.card I₁ < finset.card I₂ → ∃ (e ∈ I₂ \ I₁), (ℐ (insert e I₁))

def independent_collection (ℐ : finset (finset α)) : Prop := 
  ∀ (I₁ I₂ : finset α) (h₁ : I₁ ∈ ℐ) (h₂ : I₂ ∈ ℐ), independent ℐ I₁ I₂ h₁ h₂
-- don't love that

lemma subset_independent (ℐ ℐ': finset (finset α)) (hi : independent_collection ℐ) : 
  ℐ' ⊆ ℐ → independent_collection ℐ' :=
begin
  intros h,
  rw independent_collection,
  intros I₁ I₂ h₁ h₂,
  rw independent_collection at hi,
  --rw subset_iff at h,
  have h1' := h h₁,
  have h2' := h h₂,
  specialize hi I₁ I₂ h1' h2',
  --exact hi,
  sorry,
end

/- A matroid M is an ordered pair `(E, ℐ)` consisting of a finite set `E` and 
a collection `ℐ` of subsets of `E` having the following three properties:
  (I1) `∅ ∈ ℐ`.
  (I2) If `I ∈ ℐ` and `I' ⊆ I`, then `I' ∈ ℐ`.
  (I3) If `I₁` and `I₂` are in `I` and `|I₁| < |I₂|`, then there is an element `e` of `I₂ − I₁`
    such that `I₁ ∪ {e} ∈ I`.-/
structure matroid (E : finset α) (ℐ : finset (finset α)) :=
(subsets : ∀ (I ∈ ℐ), I ⊆ E)
(empty : ∅ ∈ ℐ) -- (I1)
(hereditary : ∀ (I₁ ∈ ℐ), ∀ (I₂ : finset α), I₂ ⊆ I₁ → I₂ ∈ ℐ) -- (I2)
(ind : independent_collection ℐ) -- (I3)


/- A subset of `E` that is not in `ℐ` is called dependent. -/ 
-- is this something that merits a separate definition?
def dependent_sets (E : finset α) (ℐ : finset (finset α)) : finset (finset α) := E.powerset \ ℐ

variables {E : finset α} {ℐ : finset (finset α)}
variables [decidable_pred (λ (D : finset α), independent_collection (erase D.powerset D))]
-- figure out where this needs to go later

namespace matroid

def circuit (M : matroid E ℐ) : finset (finset α) :=
  filter (λ (D : finset α), independent_collection (erase D.powerset D)) (dependent_sets E ℐ)

-- we're not defining n-circuits lmao

@[simp]
lemma mem_circuit (M : matroid E ℐ) (C₁ : finset α) : 
  C₁ ∈ M.circuit ↔ C₁ ∈ dependent_sets E ℐ ∧ independent_collection (erase C₁.powerset C₁) :=
begin
  rw circuit,
  rw mem_filter,
end

/- `(C1)` ∅ ∉ C  -/
lemma empty_notmem_circuit (M : matroid E ℐ) : ∅ ∉ M.circuit := 
begin
  -- this is just due to the fact that ∅ ∈ ℐ lol
  unfold matroid.circuit,
  unfold dependent_sets,
  rw mem_filter,
  rw and_comm,
  push_neg,
  intros h,
  simp,
  exact M.empty,
end

/- `(C2)` if C₁ and C₂ are members of C and C₁ ⊆ C₂, then C₂ = C₂. 
In other words, C forms an antichain. -/
lemma circuit_antichain (M : matroid E ℐ) (C₁ C₂ : finset α) (h₁ : C₁ ∈ M.circuit) (h₂ : C₂ ∈ M.circuit) :
  C₁ ⊆ C₂ → C₁ = C₂ :=
begin
  -- this is because the proper subsets are independent and therefore not in M.circuit
  intros h,
  rw mem_circuit at h₂,
  by_contra h2,
  have h3 : C₁ ∈ powerset C₂,
  { exact finset.mem_powerset.2 h },
  have h4 : C₁ ∈ C₂.powerset.erase C₂,
  { rw mem_erase,
    simp,
    exact ⟨h2, h⟩ },
  have h5 : C₁ ⊂ C₂,
  { sorry },
  
  
  sorry,
end

end matroid