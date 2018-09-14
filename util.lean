namespace util
    open classical (em prop_decidable)
    local attribute [instance] prop_decidable

    @[simp] theorem not_not_elim (P: Prop):
        ¬¬P ↔ P := begin
            apply iff.intro,
            {
                intro hnn,
                by_contra hn,
                apply hnn,
                exact hn,
            },
            {
                intros h hn,
                apply hn,
                exact h,
            },
        end

    theorem not_forall_not_elim {T: Type _} {P: T → Prop} (hnfa: ¬ ∀ x: T, ¬ P x):
        ∃ x: T, P x := begin
            by_contra hnex,
            apply hnfa,
            intro x,
            by_contra hnP,
            apply hnex,
            apply exists.intro x hnP,
        end

    @[simp] theorem not_and (A B: Prop):
        ¬(A ∧ B) ↔ ¬A ∨ ¬B := begin
            apply iff.intro,
            {
                intro hAB,
                cases (em A);
                cases (em B),
                {
                    apply false.elim,
                    apply hAB,
                    split;
                    assumption,
                },
                {
                    right,
                    assumption,
                },
                all_goals {
                    left,
                    assumption,
                },
            },
            {
                intros hor hand,
                cases hor,
                case or.inl {
                    apply hor,
                    exact hand.1,
                },
                case or.inr {
                    apply hor,
                    exact hand.2,
                },
            },
        end
end util
