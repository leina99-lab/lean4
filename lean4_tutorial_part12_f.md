# Part 12-F: 동치관계와 동치류 (Equivalence Relations and Equivalence Classes)

> **Rosen 이산수학 8판 · Section 9.5 기반**
> 『Mathematics in Lean』 + Lean 4 공식화

---

## 0. 들어가며: 이 파트에서 배울 것

이 파트에서는 **동치관계**(equivalence relation)를 다룬다. 동치관계는 수학과 컴퓨터과학에서 가장 중요한 개념 중 하나이다. "같은 종류"를 정의하는 관계이기 때문이다!

이 파트에서 다루는 내용:

1. **동치관계의 정의** — 반사적 + 대칭적 + 전이적
2. **동치류**(equivalence class) — "같은 부류"에 속하는 원소들의 집합
3. **분할**(partition) — 집합을 겹치지 않는 부분집합으로 나누기
4. **합동 클래스 모듈로 m** — 가장 유명한 동치관계
5. Lean 4에서 `Equivalence`와 `Setoid` 사용하기

### 핵심 Lean 4 개념

| 개념 | 설명 |
|------|------|
| `Equivalence` | 동치관계 증명 구조체 |
| `Setoid` | 동치관계가 부여된 타입 |
| `Set.ext` | 집합의 외연적 동치 |
| `dvd_add` | 나눗셈 분배 보조정리 |
| `rcases` | 구조 분해 전술 |

---

## 1. 동치관계란 무엇인가?

### 1.1 직관적 이해

**비유**: 학교에서 학생들을 "같은 반"으로 나누는 것을 생각해 보자.

- 학생 A는 자기 자신과 같은 반이다 (**반사적**)
- A와 B가 같은 반이면 B와 A도 같은 반이다 (**대칭적**)
- A와 B가 같은 반이고 B와 C가 같은 반이면 A와 C도 같은 반이다 (**전이적**)

이 세 가지 성질을 모두 만족하는 관계가 바로 **동치관계**이다!

### 1.2 형식적 정의

> **정의 1** (Rosen): 집합 A에 관한 관계는 이 관계가 **반사적**(reflexive), **대칭적**(symmetric), **전이적**(transitive)이면 **동치관계**(equivalence relation)라고 부른다.

| 성질 | 조건 | 의미 |
|------|------|------|
| **반사적**(reflexive) | ∀a, aRa | 모든 원소는 자기 자신과 관계 |
| **대칭적**(symmetric) | aRb → bRa | 한 방향이면 역방향도 |
| **전이적**(transitive) | aRb ∧ bRc → aRc | 이어지면 직접 연결 |

### 1.3 Lean 4에서의 정의

```lean
-- 동치관계를 직접 정의
structure IsEquivalence (R : α → α → Prop) : Prop where
  refl  : ∀ a, R a a
  symm  : ∀ a b, R a b → R b a
  trans : ∀ a b c, R a b → R b c → R a c

-- Lean 4 / Mathlib에서는 이미 Equivalence가 정의되어 있다:
-- structure Equivalence (r : α → α → Prop) where
--   refl  : ∀ x, r x x
--   symm  : ∀ {x y}, r x y → r y x
--   trans : ∀ {x y z}, r x y → r y z → r x z
```

---

## 2. 동치관계의 예

### 2.1 예제 1: 절대값이 같은 관계

R이 정수에 대한 관계이고 aRb가 "a = b 또는 a = -b"인 관계라 하자.

```lean
def absRel (a b : ℤ) : Prop := a = b ∨ a = -b

-- 반사적: a = a이므로 aRa
theorem absRel_refl (a : ℤ) : absRel a a := Or.inl rfl

-- 대칭적
theorem absRel_symm (a b : ℤ) (h : absRel a b) : absRel b a := by
  rcases h with heq | hneg
  · exact Or.inl heq.symm        -- a = b → b = a
  · right; omega                    -- a = -b → b = -a

-- 전이적
theorem absRel_trans (a b c : ℤ)
    (hab : absRel a b) (hbc : absRel b c) : absRel a c := by
  rcases hab with h1 | h1 <;> rcases hbc with h2 | h2
  · left; omega       -- a = b, b = c → a = c
  · right; omega      -- a = b, b = -c → a = -c
  · right; omega      -- a = -b, b = c → a = -c
  · left; omega       -- a = -b, b = -c → a = c

-- 종합: 동치관계이다
theorem absRel_equiv : IsEquivalence absRel :=
  ⟨absRel_refl, absRel_symm, absRel_trans⟩
```

### 2.2 예제 2: a - b가 정수인 관계

실수에서 aRb가 "a - b가 정수"인 관계라 하자. 이것도 동치관계이다:
- **반사적**: a - a = 0은 정수 ✓
- **대칭적**: a - b가 정수이면 b - a = -(a - b)도 정수 ✓
- **전이적**: a - b와 b - c가 정수이면 a - c = (a - b) + (b - c)도 정수 ✓

### 2.3 예제 3: 합동 모듈로 m — 가장 중요한 예

> R = {(a, b) | a ≡ b (mod m)}는 정수의 집합에 대한 동치관계이다.

a ≡ b (mod m)은 "m이 a - b를 나눈다"는 뜻이다. 즉 a와 b를 m으로 나눈 나머지가 같다는 것이다.

```lean
-- 합동 모듈로 m
def congMod (m : ℤ) (a b : ℤ) : Prop := m ∣ (a - b)

-- 반사적: m | (a - a) = m | 0
theorem congMod_refl (m a : ℤ) : congMod m a a := by
  simp [congMod]

-- 대칭적: m | (a - b) → m | (b - a)
theorem congMod_symm (m a b : ℤ) (h : congMod m a b) :
    congMod m b a := by
  simp [congMod] at *
  obtain ⟨k, hk⟩ := h      -- a - b = m * k
  exact ⟨-k, by linarith⟩   -- b - a = m * (-k)

-- 전이적: m | (a-b), m | (b-c) → m | (a-c)
theorem congMod_trans (m a b c : ℤ)
    (hab : congMod m a b) (hbc : congMod m b c) :
    congMod m a c := by
  simp [congMod] at *
  obtain ⟨k₁, hk₁⟩ := hab   -- a - b = m * k₁
  obtain ⟨k₂, hk₂⟩ := hbc   -- b - c = m * k₂
  exact ⟨k₁ + k₂, by linarith⟩  -- a - c = m * (k₁ + k₂)
```

### 2.4 동치관계가 아닌 예

**"나누다" 관계** (예제 6): 양의 정수에서 a | b는 반사적이고 전이적이지만, **대칭적이 아니다** (2 | 4이지만 4 ∤ 2). 따라서 동치관계가 아니다.

**|x - y| < 1 관계** (예제 7): 반사적이고 대칭적이지만, **전이적이 아니다**. x = 2.8, y = 1.9, z = 1.1이면 |x - y| = 0.9 < 1, |y - z| = 0.8 < 1이지만 |x - z| = 1.7 > 1.

---

## 3. 동치류 (Equivalence Classes)

### 3.1 정의

> **정의 3** (Rosen): R을 집합 A에 대한 동치관계라 하자. A의 원소 a와 관계가 있는 모든 원소의 집합을 a의 **동치류**(equivalence class)라 부른다. 이를 **[a]_R**로 표시한다.

**[a]_R = {s | (a, s) ∈ R}**

b ∈ [a]_R이면 b를 이 동치류의 **대표**(representative)라고 부른다.

### 3.2 예시

**절대값 동치관계의 동치류** (예제 8): [a] = {-a, a}. 예를 들어 [7] = {-7, 7}, [0] = {0}.

**합동 모듈로 4의 동치류** (예제 9):
- [0]₄ = {..., -8, -4, 0, 4, 8, ...}
- [1]₄ = {..., -7, -3, 1, 5, 9, ...}
- [2]₄ = {..., -6, -2, 2, 6, 10, ...}
- [3]₄ = {..., -5, -1, 3, 7, 11, ...}

모든 정수는 네 동치류 중 **정확하게 하나**에만 속한다!

### 3.3 Lean 4에서의 동치류

```lean
-- 동치류 정의: a와 R-동치인 모든 원소의 집합
def equivClass (R : α → α → Prop) (a : α) : Set α :=
  {x | R a x}

-- 합동 모듈로 m의 동치류
def congClass (m : ℤ) (a : ℤ) : Set ℤ :=
  {x | congMod m a x}

-- [0]₄ 에 0이 속함: 4 | (0 - 0) = 4 | 0
example : (0 : ℤ) ∈ congClass 4 0 := by
  simp [congClass, congMod]

-- [0]₄ 에 4가 속함: 4 | (0 - 4) = 4 | (-4)
example : (4 : ℤ) ∈ congClass 4 0 := by
  simp [congClass, congMod]; norm_num

-- [1]₄ 에 5가 속함: 4 | (1 - 5) = 4 | (-4)
example : (5 : ℤ) ∈ congClass 4 1 := by
  simp [congClass, congMod]; norm_num

-- [1]₄ 에 3이 속하지 않음: 4 ∤ (1 - 3) = 4 ∤ (-2)
example : (3 : ℤ) ∉ congClass 4 1 := by
  simp [congClass, congMod]; norm_num
```

---

## 4. 동치류의 핵심 성질 — 정리 1

> **정리 1** (Rosen): R이 집합 A에 대한 동치관계라 하자. 다음은 모두 **동등**하다.
>
> (i) aRb &nbsp;&nbsp;&nbsp; (ii) [a] = [b] &nbsp;&nbsp;&nbsp; (iii) [a] ∩ [b] ≠ ∅

**직관**: "두 원소가 동치" ⟺ "동치류가 같음" ⟺ "동치류가 겹침"

### 4.1 (i) → (ii) 증명: aRb → [a] = [b]

```lean
-- aRb → [a] = [b]
theorem equivClass_eq_of_related
    (R : α → α → Prop) (equiv : IsEquivalence R)
    (a b : α) (hab : R a b) :
    equivClass R a = equivClass R b := by
  ext x    -- 집합의 동치를 원소별로 증명
  constructor
  · intro hax      -- R a x
    -- R b a (대칭) + R a x → R b x (전이)
    exact equiv.trans b a x (equiv.symm a b hab) hax
  · intro hbx      -- R b x
    -- R a b + R b x → R a x (전이)
    exact equiv.trans a b x hab hbx
```

### 4.2 (ii) → (iii) 증명 스케치

[a] = [b]이면 [a] ∩ [b] = [a] ∩ [a] = [a]. 반사성에 의해 a ∈ [a]이므로 [a] ≠ ∅.

### 4.3 (iii) → (i) 증명 스케치

[a] ∩ [b] ≠ ∅이면 c ∈ [a] ∩ [b]가 존재. 즉 aRc이고 bRc. 대칭성으로 cRb. 전이성으로 aRc + cRb → aRb.

---

## 5. 분할 (Partition)

### 5.1 정의

> 집합 S의 **분할**(partition)은 S의 공집합이 아닌 서로소인 부분집합들의 모임으로, 이들의 합집합은 S이다.

조건을 정리하면:
1. 각 부분집합 Aᵢ ≠ ∅ (비어있지 않다)
2. i ≠ j이면 Aᵢ ∩ Aⱼ = ∅ (서로소이다)
3. ⋃ᵢ Aᵢ = S (합집합이 전체이다)

### 5.2 핵심 정리 — 동치관계 ↔ 분할

> **정리 2** (Rosen): R이 집합 S에 대한 동치관계라고 하자. 그러면 R의 동치류는 S의 **분할을 형성**한다. 반대로, S의 분할이 주어지면, 동치류가 그 분할의 부분집합인 동치관계가 존재한다.

이것은 매우 깊은 정리이다:
- **동치관계 → 분할**: 동치류들은 겹치지 않고 합치면 전체 집합이 된다.
- **분할 → 동치관계**: "같은 조각에 있으면 동치"로 정의하면 동치관계가 된다.

### 5.3 예제 12 (Rosen): 구체적 분할

S = {1, 2, 3, 4, 5, 6}이라 하자. A₁ = {1, 2, 3}, A₂ = {4, 5}, A₃ = {6}은 S의 분할이다.

### 5.4 예제 13 (Rosen): 분할에서 동치관계 만들기

위 분할에서의 동치관계: (a, b) ∈ R ⟺ a와 b가 같은 부분집합에 속한다.

```lean
-- 분할에 의한 동치관계
-- 각 원소가 속하는 부분집합 번호를 반환하는 함수
def partClass : Fin 6 → Fin 3
  | 0 => 0 | 1 => 0 | 2 => 0    -- {1,2,3} → 클래스 0
  | 3 => 1 | 4 => 1              -- {4,5} → 클래스 1
  | 5 => 2                        -- {6} → 클래스 2

-- 같은 클래스에 속하면 동치
def partRel (a b : Fin 6) : Prop := partClass a = partClass b

-- 반사적: partClass a = partClass a
theorem partRel_refl (a : Fin 6) : partRel a a := rfl

-- 대칭적
theorem partRel_symm (a b : Fin 6) (h : partRel a b) : partRel b a :=
  h.symm

-- 전이적
theorem partRel_trans (a b c : Fin 6)
    (hab : partRel a b) (hbc : partRel b c) : partRel a c :=
  hab.trans hbc
```

### 5.5 합동 모듈로 4의 분할

합동 모듈로 4로 생기는 네 개의 합동 클래스 [0]₄, [1]₄, [2]₄, [3]₄는 정수 집합의 분할이다. 모든 정수는 이 중 정확하게 하나에만 속한다.

---

## 6. 연습 문제 — 레벨 1: 괄호 채우기

### 연습 6.1: 동치관계 판정

```lean
-- {0, 1, 2, 3}에 대한 관계
-- R = {(0,0), (1,1), (1,3), (2,2), (2,3), (3,1), (3,2), (3,3)}
-- R이 동치관계인지 확인: (0,0)=반사, (1,3)&(3,1)=대칭, ...

-- 반사성 확인: 모든 원소 (a,a) ∈ R?
-- (0,0) ✓, (1,1) ✓, (2,2) ✓, (3,3) ✓ → 반사적

-- 대칭성 확인: (a,b)∈R이면 (b,a)∈R?
-- (1,3) → (3,1)? ✓. (2,3) → (3,2)? ✓. → 대칭적

-- 전이성 확인:
-- (1,3)∈R, (3,2)∈R → (1,2)∈R? ✗!!
-- 따라서 전이적이지 않다 → 동치관계가 아니다!

-- Lean 4로 이를 확인
def R61 : Fin 4 → Fin 4 → Prop
  | 0, 0 => True | 1, 1 => True | 1, 3 => True
  | 2, 2 => True | 2, 3 => True | 3, 1 => True
  | 3, 2 => True | 3, 3 => True | _, _ => False

-- (1,3)과 (3,2)가 R에 있지만 (1,2)는 없다 → 전이적 아님
example : R61 1 3 := by {① True를 증명하라}
example : R61 3 2 := by {② True를 증명하라}
example : ¬(R61 1 2) := by {③ False를 증명하라 — simp 사용}
```

<details>
<summary>💡 답 보기</summary>

```lean
example : R61 1 3 := trivial    -- ① R61 1 3 = True
example : R61 3 2 := trivial    -- ② R61 3 2 = True
example : ¬(R61 1 2) := by simp [R61]  -- ③ R61 1 2 = False → ¬False
```
</details>

### 연습 6.2: 합동 관계 확인

```lean
-- 12 ≡ 4 (mod 4) 확인: 4 | (12 - 4) = 4 | 8
example : congMod 4 12 4 := by
  simp [congMod]
  {④ norm_num으로 증명하라}

-- 7 ≢ 2 (mod 4) 확인: 4 ∤ (7 - 2) = 4 ∤ 5
example : ¬ congMod 4 7 2 := by
  simp [congMod]
  {⑤ norm_num으로 증명하라}
```

<details>
<summary>💡 답 보기</summary>

```lean
example : congMod 4 12 4 := by
  simp [congMod]; norm_num    -- ④

example : ¬ congMod 4 7 2 := by
  simp [congMod]; norm_num    -- ⑤
```
</details>

### 연습 6.3: 동치류 멤버십

```lean
-- [2]₃ 에 5가 속하는가? 3 | (2 - 5) = 3 | (-3) → 네!
example : (5 : ℤ) ∈ congClass 3 2 := by
  simp [congClass, congMod]
  {⑥ 적절한 전술로 증명하라}

-- [2]₃ 에 6이 속하는가? 3 | (2 - 6) = 3 | (-4) → 아니오!
example : (6 : ℤ) ∉ congClass 3 2 := by
  simp [congClass, congMod]
  {⑦ 적절한 전술로 증명하라}
```

<details>
<summary>💡 답 보기</summary>

```lean
example : (5 : ℤ) ∈ congClass 3 2 := by
  simp [congClass, congMod]; norm_num    -- ⑥

example : (6 : ℤ) ∉ congClass 3 2 := by
  simp [congClass, congMod]; norm_num    -- ⑦
```
</details>

---

## 7. 연습 문제 — 레벨 2: skeleton 채우기

### 연습 7.1: "a - b가 짝수" 관계가 동치관계임을 증명

```lean
def evenDiff (a b : ℤ) : Prop := 2 ∣ (a - b)

-- 반사적: 2 | (a - a) = 2 | 0
theorem evenDiff_refl (a : ℤ) : evenDiff a a := by
  sorry  -- simp [evenDiff] 사용

-- 대칭적: 2 | (a - b) → 2 | (b - a)
theorem evenDiff_symm (a b : ℤ) (h : evenDiff a b) :
    evenDiff b a := by
  sorry  -- obtain, linarith 사용

-- 전이적
theorem evenDiff_trans (a b c : ℤ)
    (hab : evenDiff a b) (hbc : evenDiff b c) :
    evenDiff a c := by
  sorry  -- obtain, linarith 사용
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem evenDiff_refl (a : ℤ) : evenDiff a a := by
  simp [evenDiff]

theorem evenDiff_symm (a b : ℤ) (h : evenDiff a b) :
    evenDiff b a := by
  simp [evenDiff] at *
  obtain ⟨k, hk⟩ := h
  exact ⟨-k, by linarith⟩

theorem evenDiff_trans (a b c : ℤ)
    (hab : evenDiff a b) (hbc : evenDiff b c) :
    evenDiff a c := by
  simp [evenDiff] at *
  obtain ⟨k₁, hk₁⟩ := hab
  obtain ⟨k₂, hk₂⟩ := hbc
  exact ⟨k₁ + k₂, by linarith⟩
```
</details>

### 연습 7.2: 같은 동치류에 속하면 동치

```lean
-- c ∈ [a] 이고 c ∈ [b] 이면 aRb
theorem related_of_common_member
    (R : α → α → Prop) (equiv : IsEquivalence R)
    (a b c : α)
    (hac : R a c) (hbc : R b c) : R a b := by
  sorry
  -- 힌트: hbc의 대칭성으로 R c b를 얻고, hac과 전이성으로 R a b
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem related_of_common_member
    (R : α → α → Prop) (equiv : IsEquivalence R)
    (a b c : α)
    (hac : R a c) (hbc : R b c) : R a b := by
  exact equiv.trans a c b hac (equiv.symm b c hbc)
```

**설명**: R a c (가정) + R c b (hbc의 대칭) → R a b (전이성)
</details>

### 연습 7.3: 분할에 의한 관계가 동치관계임

```lean
-- 함수 f에 의해 정의된 관계: f(a) = f(b)이면 동치
def funcRel (f : α → β) (a b : α) : Prop := f a = f b

-- 이 관계가 동치관계임을 증명
theorem funcRel_equiv (f : α → β) : IsEquivalence (funcRel f) := by
  constructor
  · intro a; exact rfl                              -- 반사적
  · intro a b h; sorry                               -- 대칭적
  · intro a b c hab hbc; sorry                       -- 전이적
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem funcRel_equiv (f : α → β) : IsEquivalence (funcRel f) := by
  constructor
  · intro a; exact rfl
  · intro a b h; exact h.symm
  · intro a b c hab hbc; exact hab.trans hbc
```

**설명**: `funcRel f a b = (f a = f b)`이므로, 등식의 반사성/대칭성/전이성을 그대로 사용할 수 있다. 이것은 매우 일반적인 패턴이다: **임의의 함수 f에 대해 "f(a) = f(b)" 관계는 항상 동치관계이다!**
</details>

---

## 8. 연습 문제 — 레벨 3: sorry 채우기 (독립 증명)

### 연습 8.1: 합동 모듈로 m 동치관계 종합

```lean
-- 합동 모듈로 m이 동치관계임을 하나의 정리로 증명
theorem congMod_isEquiv (m : ℤ) : IsEquivalence (congMod m) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem congMod_isEquiv (m : ℤ) : IsEquivalence (congMod m) :=
  ⟨congMod_refl m, congMod_symm m, congMod_trans m⟩
```
</details>

### 연습 8.2: 동치류가 같으면 동치 ((ii) → (i) 방향)

```lean
-- [a] = [b] → aRb
theorem related_of_equivClass_eq
    (R : α → α → Prop) (equiv : IsEquivalence R) (a b : α)
    (h : equivClass R a = equivClass R b) : R a b := by
  sorry
  -- 힌트: a ∈ [a] (반사성), h에 의해 a ∈ [b], 즉 R b a
  -- 대칭성으로 R a b
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem related_of_equivClass_eq
    (R : α → α → Prop) (equiv : IsEquivalence R) (a b : α)
    (h : equivClass R a = equivClass R b) : R a b := by
  -- a ∈ [a]_R (반사성)
  have ha : a ∈ equivClass R a := equiv.refl a
  -- h에 의해 a ∈ [b]_R
  rw [h] at ha
  -- ha : R b a
  exact equiv.symm b a ha
```
</details>

### 연습 8.3: "나누다"가 동치관계가 아님을 증명 (도전!)

```lean
-- 양의 정수에서 "나누다" 관계는 동치관계가 아니다
-- 대칭적이 아닌 반례를 들면 된다
theorem divides_not_symm :
    ¬ (∀ a b : ℕ, a ∣ b → b ∣ a) := by
  sorry
  -- 힌트: push_neg, use 2, use 4
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem divides_not_symm :
    ¬ (∀ a b : ℕ, a ∣ b → b ∣ a) := by
  push_neg
  use 2, 4
  constructor
  · norm_num    -- 2 | 4
  · norm_num    -- ¬(4 | 2)
```

**설명**: `push_neg`은 ¬∀를 ∃¬로 변환한다. 반례로 a = 2, b = 4를 제시하면, 2 | 4이지만 4 ∤ 2이다.
</details>

### 연습 8.4: 동치류의 대표는 아무나 될 수 있다

```lean
-- b ∈ [a] → [a] = [b]
-- 즉, 동치류의 어떤 원소도 대표가 될 수 있다
theorem equivClass_rep (R : α → α → Prop) (equiv : IsEquivalence R)
    (a b : α) (h : b ∈ equivClass R a) :
    equivClass R a = equivClass R b := by
  sorry
  -- 힌트: h는 R a b이다. equivClass_eq_of_related를 사용하라.
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem equivClass_rep (R : α → α → Prop) (equiv : IsEquivalence R)
    (a b : α) (h : b ∈ equivClass R a) :
    equivClass R a = equivClass R b :=
  equivClass_eq_of_related R equiv a b h
```
</details>

---

## 9. 부분순서 맛보기 (Partial Orders Preview)

### 9.1 정의

> **정의 1** (Rosen 9.6): 집합 S에 대한 관계 R이 **반사적**(reflexive), **반대칭적**(antisymmetric), **전이적**(transitive)이면 **부분순서**(partial order)라고 부른다.

동치관계와 비교해 보자:

| | **동치관계** | **부분순서** |
|---|---|---|
| 반사적 | ✓ | ✓ |
| 대칭적 | ✓ | ✗ (반대칭적) |
| 전이적 | ✓ | ✓ |

핵심 차이: 동치관계는 **대칭적**이지만, 부분순서는 **반대칭적**이다!

### 9.2 부분순서의 예

- ℕ 위의 **≤** 관계: 반사적(a ≤ a), 반대칭적(a ≤ b, b ≤ a → a = b), 전이적 → **부분순서**
- 집합의 **⊆** 관계: 반사적(A ⊆ A), 반대칭적(A ⊆ B, B ⊆ A → A = B), 전이적 → **부분순서**
- 양의 정수의 **|** (나누다) 관계: 반사적, 반대칭적, 전이적 → **부분순서**

### 9.3 Lean 4에서의 부분순서

```lean
-- Lean 4에서 부분순서는 PartialOrder 타입 클래스로 표현된다
-- 이미 ℕ, ℤ, ℝ 등에 PartialOrder 인스턴스가 있다

-- 기본 성질
variable {α : Type*} [PartialOrder α] (a b c : α)

-- 반사적
#check (le_refl a : a ≤ a)

-- 반대칭적
#check (le_antisymm : a ≤ b → b ≤ a → a = b)

-- 전이적
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

-- 엄격 부분순서 (strict partial order)
-- a < b ↔ a ≤ b ∧ a ≠ b
example : a < b ↔ a ≤ b ∧ a ≠ b := lt_iff_le_and_ne
```

이 내용은 Part 12-G에서 더 자세히 다룰 예정이다.

---

## 10. 핵심 요약

1. **동치관계**(equivalence relation)는 반사적 + 대칭적 + 전이적인 관계이다.
2. **동치류**(equivalence class) [a]_R = {s | aRs}는 a와 동치인 모든 원소의 집합이다.
3. **정리 1**: aRb ⟺ [a] = [b] ⟺ [a] ∩ [b] ≠ ∅.
4. **분할**(partition)은 비어있지 않고 서로소인 부분집합들의 모음으로 합집합이 전체인 것이다.
5. **정리 2**: 동치관계 ↔ 분할 (일대일 대응).
6. **합동 모듈로 m**: a ≡ b (mod m) ⟺ m | (a - b). 가장 중요한 동치관계.
7. Lean 4에서 `IsEquivalence`는 `refl`, `symm`, `trans` 세 필드를 갖는 구조체이다.
8. 함수 f에 의한 관계 "f(a) = f(b)"는 항상 동치관계이다.
9. **부분순서**(partial order)는 반사적 + **반대칭적** + 전이적인 관계이다 (동치관계와 비교!).

---

## 11. 사용된 Lean 4 전술 정리

| 전술 | 용도 | 예시 |
|------|------|------|
| `Or.inl` / `Or.inr` | ∨의 좌/우 증명 | `Or.inl rfl` |
| `rcases h with h1 \| h2` | ∨ 분해 | 경우 나누기 |
| `obtain ⟨k, hk⟩ := h` | ∃ 분해 | `h : m ∣ n`에서 k 추출 |
| `ext x` | 집합/함수 외연성 | `equivClass R a = equivClass R b` |
| `linarith` | 선형 산술 | 정수 부등식/등식 |
| `omega` | 자연수/정수 산술 | 간단한 산술 |
| `norm_num` | 수치 계산 | `4 ∣ (-4)` |
| `push_neg` | ¬∀ → ∃¬ 변환 | 반례 증명 |
| `simp [f]` | 정의 펼치기 + 단순화 | `simp [congMod]` |
| `trivial` | True 등 간단한 증명 | `(trivial : R 0 0)` |

---

> **다음 파트 예고**: Part 12-G에서는 **부분순서**(partial orders)를 본격적으로 다룬다. 하세 도표(Hasse diagram), 최대/최소 원소, 상한/하한, **격자**(lattice), 그리고 **위상정렬**(topological sort)을 Lean 4로 구현한다!
