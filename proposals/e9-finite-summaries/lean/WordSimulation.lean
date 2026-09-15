/-
UNCOMPILED CANDIDATE SOURCE. No Lean executable was available for this study.
This file is a proposed reusable semantic lemma, NOT a reflected matrix checker
and NOT an implemented forge tactic. Compile and audit before importing it.
-/
set_option autoImplicit false
namespace ForgeFiniteSummaries
universe u v w z

def run {A : Type u} {S : Type v} (step : S → A → S) : S → List A → S
  | s, [] => s
  | s, a :: rest => run step (step s a) rest

theorem run_simulation
    {A : Type u} {S : Type v} {T : Type w}
    (step : S → A → S) (smallStep : T → A → T) (embed : T → S)
    (hstep : ∀ t a, step (embed t) a = embed (smallStep t a)) :
    ∀ word t, run step (embed t) word = embed (run smallStep t word) := by
  intro word
  induction word with
  | nil =>
      intro t
      rfl
  | cons a rest ih =>
      intro t
      change run step (step (embed t) a) rest =
        embed (run smallStep (smallStep t a) rest)
      rw [hstep]
      exact ih (smallStep t a)

theorem observation_of_summary
    {A : Type u} {S : Type v} {T : Type w} {O : Type z}
    (step : S → A → S) (smallStep : T → A → T) (embed : T → S)
    (observe : S → O) (wanted : O) (initial : S) (seed : T)
    (hinit : initial = embed seed)
    (hstep : ∀ t a, step (embed t) a = embed (smallStep t a))
    (hout : ∀ t, observe (embed t) = wanted) (word : List A) :
    observe (run step initial word) = wanted := by
  rw [hinit, run_simulation step smallStep embed hstep]
  exact hout (run smallStep seed word)

#print axioms run_simulation
#print axioms observation_of_summary
end ForgeFiniteSummaries
