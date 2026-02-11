# 📝 Lean 4 연습문제 모음 — Part 1 ~ 3 범위 · 명제와 증명 완전 정복

> **lean4_tutorial_part1.md ~ part3.md 범위 내 · 명제**(Prop) **중심**
>
> **괄호 채우기** 20문제 + **sorry 채우기** 20문제 (괄호 문제를 sorry로 변환한 것 포함)

---

## 📖 이 연습문제에서 사용하는 전략(tactic) — Part 1~3 범위만


| 전략(tactic) | 배운 곳 | 하는 일 |
|-------------|---------|--------|
| `rw [h]` | Part 1 | 등식 `h`로 목표를 **치환**(바꿔치기) |
| `rw [← h]` | Part 1 | 등식 `h`의 **역방향**으로 치환 |
| `rw [h] at hyp` | Part 1 | **가설**(hyp) 안에서 치환 |
| `ring` | Part 1 | 산술 등식 **자동** 증명 |
| `rfl` | Part 1 | 양변이 **정의상 같을 때** 증명 |
| `exact h` | Part 1 | 가설 `h`가 목표와 **정확히** 일치 |
| `calc` | Part 1 | 단계별 **계산** 증명 |
| `sorry` | Part 1 | 아직 미완성 (빈칸) |
| `norm_num` | Part 2 | 구체적 **숫자 계산** 자동 증명 |
| `apply f` | Part 2 | 정리 `f`를 **적용** |
| `linarith` | Part 2 | **선형 부등식** 자동 증명 |
| `nth_rw n [h]` | Part 2 | **n번째** 매칭만 치환 |
| `intro h` | Part 3 | **가정 도입** ("~라 하자") |
| `constructor` | Part 3 | `∧` 또는 `↔`를 **두 목표로 분리** |
| `left` / `right` | Part 3 | `∨`의 왼쪽/오른쪽 **선택** |
| `use 값` | Part 3 | `∃`의 **증인 제시** |
| `rcases h with ⟨a, b⟩` | Part 3 | 가설을 **분해** |
| `rintro ⟨a, b⟩` | Part 3 | 도입 + 분해 **동시에** |
| `.mp` / `.mpr` | Part 3 | `↔`의 정방향/역방향 **추출** |

> `push_neg`, `contrapose`, `by_contra`, `exfalso`, `contradiction`은 Part 3 **후반**에 나오지만, 이 문제집에서는 **사용하지 않는다**. 위 표의 전략만으로 모든 문제를 풀 수 있다.

---


# 🅰️ 괄호 채우기 연습문제 (20문제)

> `[????]` 부분을 올바른 내용으로 채워 넣으시오.

---

### B-01. `rfl` — 정의상 같음

```lean
theorem two_plus_three : 2 + 3 = 5 := [????]
```

<details>
<summary>✅ 정답</summary>

```lean
theorem two_plus_three : 2 + 3 = 5 := rfl
```
`2 + 3`을 계산하면 `5`이고, `5 = 5`이므로 `rfl`(반사성)로 증명된다.
</details>

---

### B-02. `rw` 기본 — 교환법칙

```lean
variable (a b c : ℝ)

example : a * b * c = b * a * c := by
  rw [[????]]
```

<details>
<summary>✅ 정답</summary>

```lean
  rw [mul_comm a b]
```
`a * b`를 `b * a`로 치환한다. 그러면 양변이 `b * a * c`로 같아져 증명이 끝난다.
</details>

---

### B-03. `rw` 연속 — 여러 단계 치환

```lean
variable (a b c : ℝ)

example : a * b * c = b * (a * c) := by
  rw [[????]]
  rw [[????]]
```

<details>
<summary>✅ 정답</summary>

```lean
  rw [mul_comm a b]
  rw [mul_assoc b a c]
```
1단계: `a * b`를 `b * a`로 → 목표가 `b * a * c = b * (a * c)`
2단계: `b * a * c`를 `b * (a * c)`로(결합법칙) → 양변 동일. 끝!
</details>

---

### B-04. `rw` 역방향 — `←` 사용

```lean
variable (a b c : ℝ)

example : a * (b * c) = a * b * c := by
  rw [[????] mul_assoc a b c]
```

<details>
<summary>✅ 정답</summary>

```lean
  rw [← mul_assoc a b c]
```
`mul_assoc`는 `a * b * c = a * (b * c)`이다. `←`로 역방향 적용하면 `a * (b * c)`를 `a * b * c`로 바꾼다.
</details>

---

### B-05. `rw at` — 가설에서 치환

```lean
variable (a b c d : ℝ)

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [[????]] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp
```

<details>
<summary>✅ 정답</summary>

```lean
  rw [hyp'] at hyp
```
`hyp'`는 `b = a * d`이므로, `hyp` 안의 `b`가 `a * d`로 치환된다.
</details>

---

### B-06. `ring` — 자동 증명

```lean
variable (a b : ℝ)

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  [????]
```

<details>
<summary>✅ 정답</summary>

```lean
  ring
```
`ring`은 환(ring) 공리만으로 증명 가능한 등식을 자동 해결한다.
</details>

---

### B-07. `calc` — 단계별 증명

```lean
variable (a b c : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [[????], ← two_mul]
```

<details>
<summary>✅ 정답</summary>

```lean
      rw [mul_comm b a, ← two_mul]
```
`b * a`를 `a * b`로 바꿔야 `b * a + a * b`가 `a * b + a * b = 2 * (a * b)`로 정리된다.
</details>

---

### B-08. `exact` — 정확히 일치

```lean
variable (a b : ℝ)

example (h : a = b) : a = b := by
  [????] h
```

<details>
<summary>✅ 정답</summary>

```lean
  exact h
```
가설 `h : a = b`가 목표 `a = b`와 정확히 일치하므로 `exact h`로 끝난다.
</details>

---

### B-09. `apply` — 정리 적용

```lean
variable (a b c : ℝ)

example (h₀ : a ≤ b) (h₁ : b ≤ c) : a ≤ c := by
  [????] le_trans h₀ h₁
```

<details>
<summary>✅ 정답</summary>

```lean
  exact le_trans h₀ h₁
```
`le_trans`는 `a ≤ b → b ≤ c → a ≤ c`이다. `h₀`과 `h₁`을 넣으면 바로 증명된다. `apply le_trans h₀ h₁` 또는 `exact le_trans h₀ h₁` 둘 다 가능하다.
</details>

---

### B-10. `intro` — 함의(→) 증명 시작

```lean
variable (P Q : Prop)

example (h : P → Q) (hp : P) : Q := by
  [????] h hp
```

<details>
<summary>✅ 정답</summary>

```lean
  exact h hp
```
`h`는 `P → Q`(P이면 Q) 타입의 함수이고, `hp`는 `P`의 증명이다. `h hp`는 "P의 증명을 넣어서 Q의 증명을 얻는다"는 뜻이다.
</details>

---

### B-11. `intro` — 직접 함의 증명하기

```lean
variable (P : Prop)

example : P → P := by
  [????] h
  exact h
```

<details>
<summary>✅ 정답</summary>

```lean
  intro h
```
`intro h`는 "P가 참이라고 가정하자. 그 증거를 `h`라고 부르겠다"는 뜻이다. 그러면 목표가 `P`가 되고, `h : P`가 있으므로 `exact h`로 끝.
</details>

---

### B-12. `constructor` — 논리곱(∧) 증명

```lean
variable (P Q : Prop)

example (hp : P) (hq : Q) : P ∧ Q := by
  [????]
  · exact hp
  · exact hq
```

<details>
<summary>✅ 정답</summary>

```lean
  constructor
```
`constructor`는 `P ∧ Q`를 두 목표 `P`와 `Q`로 나눈다. 각각을 `·` 블록에서 증명한다.
</details>

---

### B-13. `rcases` — 논리곱(∧) 분해

```lean
variable (P Q : Prop)

example (h : P ∧ Q) : P := by
  [????] h with ⟨hp, hq⟩
  exact hp
```

<details>
<summary>✅ 정답</summary>

```lean
  rcases h with ⟨hp, hq⟩
```
`rcases`는 `P ∧ Q`를 `hp : P`와 `hq : Q`로 분해한다. 우리는 `P`만 필요하므로 `exact hp`.
</details>

---

### B-14. `left` / `right` — 논리합(∨) 증명

```lean
variable (P Q : Prop)

example (hp : P) : P ∨ Q := by
  [????]
  exact hp
```

<details>
<summary>✅ 정답</summary>

```lean
  left
```
`P ∨ Q`를 증명할 때, `P`를 증명하겠다면 `left`, `Q`를 증명하겠다면 `right`를 쓴다.
</details>

---

### B-15. `use` — 존재 양화사(∃) 증명

```lean
example : ∃ n : ℕ, n + 1 = 4 := by
  [????] 3
  rfl
```

<details>
<summary>✅ 정답</summary>

```lean
  use 3
```
`use 3`은 "n = 3이 존재한다!"고 선언한다. 그러면 목표가 `3 + 1 = 4`가 되고, `rfl`로 끝.
</details>

---

### B-16. `constructor` — 동치(↔) 증명

```lean
variable (P : Prop)

example : P ↔ P := by
  [????]
  · intro h; exact h
  · intro h; exact h
```

<details>
<summary>✅ 정답</summary>

```lean
  constructor
```
`P ↔ P`는 `(P → P) ∧ (P → P)`이므로, `constructor`로 두 방향을 나눠 각각 증명한다.
</details>

---

### B-17. `.mp` — 동치의 정방향 추출

```lean
variable (P Q : Prop)

example (h : P ↔ Q) (hp : P) : Q := by
  exact h.[????] hp
```

<details>
<summary>✅ 정답</summary>

```lean
  exact h.mp hp
```
`.mp`는 `P ↔ Q`에서 **정방향** `P → Q`를 추출한다. `hp : P`를 넣으면 `Q`의 증명을 얻는다.
</details>

---

### B-18. `.mpr` — 동치의 역방향 추출

```lean
variable (P Q : Prop)

example (h : P ↔ Q) (hq : Q) : P := by
  exact h.[????] hq
```

<details>
<summary>✅ 정답</summary>

```lean
  exact h.mpr hq
```
`.mpr`은 `P ↔ Q`에서 **역방향** `Q → P`를 추출한다.
</details>

---

### B-19. `rintro` — 도입 + 분해 동시에

```lean
variable (P Q R : Prop)

example : (P ∧ Q) → P := by
  [????] ⟨hp, hq⟩
  exact hp
```

<details>
<summary>✅ 정답</summary>

```lean
  rintro ⟨hp, hq⟩
```
`rintro`는 `intro` + `rcases`를 합친 것이다. `P ∧ Q`를 도입하면서 동시에 `hp`와 `hq`로 분해한다.
</details>

---

### B-20. `norm_num` — 숫자 계산

```lean
example : (3 : ℕ) + 7 = 10 := by
  [????]
```

<details>
<summary>✅ 정답</summary>

```lean
  norm_num
```
`norm_num`은 구체적인 숫자 계산을 자동으로 처리한다. `rfl`도 되지만, 복잡한 숫자일수록 `norm_num`이 더 확실하다.
</details>

---

---

# 🅱️ sorry 채우기 연습문제 (20문제)

> `sorry`를 지우고 완전한 증명을 작성하시오.
> 위 괄호 문제를 sorry 형식으로 변환한 것 + 새로운 문제가 포함되어 있다.

---

### S-01. `rfl` — 간단한 등식

```lean
theorem three_times_two : 3 * 2 = 6 := by
  sorry
```

<details>
<summary>✅ 정답</summary>

```lean
theorem three_times_two : 3 * 2 = 6 := rfl
```
또는 `by norm_num` 또는 `by rfl`
</details>

---

### S-02. `rw` — 교환법칙 한 번

```lean
variable (a b : ℝ)

example : a + b = b + a := by
  sorry
```

<details>
<summary>✅ 정답</summary>

```lean
  rw [add_comm]
```
또는 `ring`
</details>

---

### S-03. `rw` — 교환법칙 + 결합법칙 조합

```lean
variable (a b c : ℝ)

example : a * b * c = b * (a * c) := by
  sorry
```

<details>
<summary>✅ 정답</summary>

```lean
  rw [mul_comm a b]
  rw [mul_assoc b a c]
```
또는 `ring`
</details>

---

### S-04. `rw at` + `exact` — 가설 치환 후 마무리

```lean
variable (a b c d : ℝ)

example (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry
```

<details>
<summary> 힌트</summary>
`hyp'`를 `hyp`에 대입 → `mul_comm` 적용 → `sub_self` 적용 → `exact hyp`
</details>

<details>
<summary>✅ 정답</summary>

```lean
  rw [hyp', mul_comm a b] at hyp
  rw [sub_self] at hyp
  exact hyp
```
</details>

---

### S-05. `ring` — 전개 공식

```lean
variable (a b : ℝ)

example : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  sorry
```

<details>
<summary>✅ 정답</summary>

```lean
  ring
```
</details>

---

### S-06. `P → P` — 항등 함의

```lean
variable (P : Prop)

example : P → P := by
  sorry
```

<details>
<summary>✅ 정답</summary>

```lean
  intro h
  exact h
```
"P가 참이라 하자 → 그러면 P는 참이다." 가장 단순한 함의 증명이다.
</details>

---

### S-07. `P → Q → P` — 약화(weakening)

```lean
variable (P Q : Prop)

example : P → Q → P := by
  sorry
```

<details>
<summary> 힌트</summary>
`intro`를 두 번 쓴다. 첫 번째로 P의 증거를, 두 번째로 Q의 증거를 도입한다. Q는 안 쓰고 P만 반환하면 된다.
</details>

<details>
<summary>✅ 정답</summary>

```lean
  intro hp hq
  exact hp
```
</details>

---

### S-08. 논리곱(∧) 만들기

```lean
variable (P Q : Prop)

example (hp : P) (hq : Q) : P ∧ Q := by
  sorry
```

<details>
<summary>✅ 정답</summary>

```lean
  constructor
  · exact hp
  · exact hq
```
또는 한 줄로: `exact ⟨hp, hq⟩`
</details>

---

### S-09. 논리곱(∧) 분해 — 왼쪽 추출

```lean
variable (P Q : Prop)

example (h : P ∧ Q) : P := by
  sorry
```

<details>
<summary>✅ 정답</summary>

```lean
  rcases h with ⟨hp, hq⟩
  exact hp
```
또는: `exact h.1` (`.1`은 ∧의 왼쪽)
</details>

---

### S-10. 논리곱(∧) 분해 — 오른쪽 추출

```lean
variable (P Q : Prop)

example (h : P ∧ Q) : Q := by
  sorry
```

<details>
<summary>✅ 정답</summary>

```lean
  exact h.2
```
또는: `rcases h with ⟨hp, hq⟩; exact hq`
</details>

---

### S-11. 논리곱(∧) 교환

```lean
variable (P Q : Prop)

example (h : P ∧ Q) : Q ∧ P := by
  sorry
```

<details>
<summary> 힌트</summary>
`rcases`로 분해한 뒤, `constructor`로 순서를 바꿔서 다시 합친다.
</details>

<details>
<summary>✅ 정답</summary>

```lean
  rcases h with ⟨hp, hq⟩
  constructor
  · exact hq
  · exact hp
```
또는: `exact ⟨h.2, h.1⟩`
</details>

---

### S-12. 논리합(∨) — 왼쪽에서 증명

```lean
variable (P Q : Prop)

example (hp : P) : P ∨ Q := by
  sorry
```

<details>
<summary>✅ 정답</summary>

```lean
  left
  exact hp
```
</details>

---

### S-13. 논리합(∨) — 오른쪽에서 증명

```lean
variable (P Q : Prop)

example (hq : Q) : P ∨ Q := by
  sorry
```

<details>
<summary>✅ 정답</summary>

```lean
  right
  exact hq
```
</details>

---

### S-14. 존재 양화사(∃) — 증인 제시

```lean
example : ∃ n : ℕ, 2 * n = 8 := by
  sorry
```

<details>
<summary>✅ 정답</summary>

```lean
  use 4
```
`use 4`로 n = 4를 제시하면 목표가 `2 * 4 = 8`이 되고, Lean이 자동으로 계산해서 끝낸다.
</details>

---

### S-15. 존재 양화사(∃) — 분해해서 사용

```lean
variable (P : ℕ → Prop)

example (h : ∃ n, P n ∧ n = 3) : ∃ n, P n := by
  sorry
```

<details>
<summary> 힌트</summary>
`rcases h with ⟨n, hpn, hn⟩`로 분해하면 `n`, `hpn : P n`, `hn : n = 3`을 얻는다. 그 n을 `use`한다.
</details>

<details>
<summary>✅ 정답</summary>

```lean
  rcases h with ⟨n, hpn, hn⟩
  use n
  exact hpn
```
또는: `exact ⟨_, h.choose_spec.1⟩` (고급)
</details>

---

### S-16. `↔` 증명 — 양방향 각각

```lean
variable (P Q : Prop)

example (hpq : P → Q) (hqp : Q → P) : P ↔ Q := by
  sorry
```

<details>
<summary>✅ 정답</summary>

```lean
  constructor
  · exact hpq
  · exact hqp
```
또는: `exact ⟨hpq, hqp⟩`
</details>

---

### S-17. `↔` 사용 — `.mp`와 `.mpr`

```lean
variable (P Q : Prop)

example (h : P ↔ Q) (hp : P) : Q := by
  sorry
```

<details>
<summary>✅ 정답</summary>

```lean
  exact h.mp hp
```
`.mp`는 ↔의 **정방향**(P → Q)을 추출한다.
</details>

---

### S-18. `↔` 교환

```lean
variable (P Q : Prop)

example (h : P ↔ Q) : Q ↔ P := by
  sorry
```

<details>
<summary> 힌트</summary>
`constructor`로 나누고, `.mp`와 `.mpr`을 적절히 쓴다.
</details>

<details>
<summary>✅ 정답</summary>

```lean
  constructor
  · exact h.mpr
  · exact h.mp
```
또는: `exact h.symm` (Lean이 제공하는 대칭성)
</details>

---

### S-19. 함의 합성 — `P → Q`와 `Q → R`에서 `P → R`

```lean
variable (P Q R : Prop)

example (hpq : P → Q) (hqr : Q → R) : P → R := by
  sorry
```

<details>
<summary> 힌트</summary>
`intro hp`로 P의 증명을 도입 → `hpq hp`로 Q의 증명을 얻고 → `hqr`에 넣어 R의 증명을 얻는다.
</details>

<details>
<summary>✅ 정답</summary>

```lean
  intro hp
  exact hqr (hpq hp)
```
또는:
```lean
  intro hp
  apply hqr
  apply hpq
  exact hp
```
</details>

---

### S-20. 종합 — `∧`, `→`, `∃` 조합

```lean
example : (∃ n : ℕ, n > 0) ∧ (2 + 3 = 5) := by
  sorry
```

<details>
<summary> 힌트</summary>
`constructor`로 `∧`를 나누고, 왼쪽은 `use`로 존재 양화사를 해결, 오른쪽은 `norm_num`으로 계산.
</details>

<details>
<summary>✅ 정답</summary>

```lean
  constructor
  · use 1
  · norm_num
```
</details>

---

---

## 📋 문제 대응표: "이 괄호 문제를 sorry로 풀어보세요"

괄호 문제를 풀었다면, 같은 명제를 sorry 형식으로도 풀어보자!

| 괄호 문제 | → sorry로 풀기 |
|----------|---------------|
| B-01 (`rfl`) | S-01과 동일 유형 |
| B-02 (`rw` 기본) | S-02와 동일 유형 |
| B-03 (`rw` 연속) | S-03과 동일 유형 |
| B-04 (`←` 역방향) | S-03에서 연습 |
| B-05 (`rw at`) | S-04와 동일 유형 |
| B-06 (`ring`) | S-05와 동일 유형 |
| B-08 ~ B-09 | S-06, S-07 (함의) |
| B-10 ~ B-11 | S-06, S-07, S-19 (함의 심화) |
| B-12 ~ B-13 | S-08 ~ S-11 (논리곱) |
| B-14 | S-12, S-13 (논리합) |
| B-15 | S-14, S-15 (존재 양화사) |
| B-16 ~ B-18 | S-16 ~ S-18 (동치) |
| B-19 | S-11 (rintro 활용) |
| B-20 | S-20과 동일 유형 |

---

>  **이 40문제를 다 풀 수 있다면**, Part 1~3에서 배운 명제와 증명의 핵심을 **완전히 체득**한 것이다. 다음 단계(Part 4: 집합과 함수)로 넘어갈 준비가 되었다!
