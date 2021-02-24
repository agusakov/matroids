import data.finset

universes u

open finset

variables {α : Type u} [decidable_eq α] [fintype α]

/- A matroid M is an ordered pair `(E, ℐ)` consisting of a finite set `E` and 
a collection `ℐ` of subsets of `E` having the following three properties:
  (I1) `∅ ∈ ℐ`.
  (I2) If `I ∈ ℐ` and `I' ⊆ I`, then `I' ∈ ℐ`.
  (I3) If `I₁` and `I₂` are in `I` and `|I₁| < |I₂|`, then there is an element `e` of `I₂ − I₁`
    such that `I₁ ∪ {e} ∈ I`.-/

-- could i define independence inductively?
-- in linear_independent.lean, independence is defined w.r.t. finsupp and the kernel, interesting
def can_exchange (ℐ : finset α → Prop) : Prop := 
∀ I₁ I₂, ℐ I₁ ∧ ℐ I₂ → finset.card I₁ < finset.card I₂ → ∃ (e ∈ I₂ \ I₁), (ℐ (insert e I₁))

@[ext]
structure matroid (α : Type u) [fintype α] [decidable_eq α] :=
(ℐ : finset α → Prop)
(empty : ℐ ∅) -- (I1)
(hereditary : ∀ (I₁ : finset α), ℐ I₁ → ∀ (I₂ : finset α), I₂ ⊆ I₁ → ℐ I₂) -- (I2)
(ind : can_exchange ℐ) -- (I3)


namespace matroid

variables (M : matroid α) [decidable_pred M.ℐ]

/- A subset of `E` that is not in `ℐ` is called dependent. -/ 
def dependent_sets : finset (finset α) := filter (λ s, ¬ M.ℐ s) univ.powerset

-- (C1)
lemma empty_not_dependent : ∅ ∉ M.dependent_sets :=
begin
  have h1 := M.empty,
  rw dependent_sets,
  simp,
  exact h1,
end

variables [decidable_pred (λ (D : finset α), can_exchange (λ (_x : finset α), _x ∈ D.powerset.erase D))]

def circuit : finset (finset α) :=
  finset.filter (λ (D : finset α), (∀ (S ∈ (erase D.powerset D)), M.ℐ S)) (M.dependent_sets)


@[simp]
lemma mem_circuit (C₁ : finset α) : 
  C₁ ∈ M.circuit ↔ C₁ ∈ M.dependent_sets ∧ (∀ (C₂ ∈ (erase C₁.powerset C₁)), M.ℐ C₂) :=
begin
  rw circuit,
  rw dependent_sets,
  rw mem_filter,
end

/- `(C2)` if C₁ and C₂ are members of C and C₁ ⊆ C₂, then C₂ = C₂. 
In other words, C forms an antichain. -/
lemma circuit_antichain (C₁ C₂ : finset α) (h₁ : C₁ ∈ M.circuit) (h₂ : C₂ ∈ M.circuit) : C₁ ⊆ C₂ → C₁ = C₂ :=
begin
  intros h,
  -- every proper subset of C₂ is independent
  -- then either C₁ is independent or C₁ = C₂
  rw circuit at h₂,
  simp at h₂,
  have h2 := h₂.2,
  by_contra h3,
  specialize h2 C₁ h3 h,
  rw circuit at h₁,
  rw mem_filter at h₁,
  have h1 := h₁.1,
  rw dependent_sets at h1,
  rw mem_filter at h1,
  apply h1.2,
  exact h2,
end 

/- `(C3)` If C₁ and C₂ are distinct members of M.circuit and e ∈ C₁ ∩ C₂, then
there is a member C₃ of M.circuit such that C₃ ⊆ (C₁ ∪ C₂) - e.   -/
lemma circuit_dependence (C₁ C₂ : finset α) (h₁ : C₁ ∈ M.circuit) (h₂ : C₂ ∈ M.circuit) (h : C₁ ≠ C₂) (e : α) :
  e ∈ C₁ ∩ C₂ → ∃ C₃ ∈ M.circuit, C₃ ⊆ (C₁ ∪ C₂) \ {e} :=
begin
  intros h,
  sorry,
end

end matroid