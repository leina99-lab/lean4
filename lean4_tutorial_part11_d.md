# Lean4 완전 정복 가이드 —  Part 11-D: 포함-배제 원리 (Inclusion-Exclusion Principle)

> **Rosen 『이산수학』 8판 8.5–8.6절** 기반  
> **선수 지식**: Part 5-D (집합론 기초), Part 11-C (생성 함수 기초)  
> **목표**: 포함-배제 원리를 이해하고, Lean 4의 `Finset` 연산으로 형식화하는 방법을 익힌다.

---

## 0. 이 파트에서 배울 핵심 개념

| 개념 | 설명 |
|------|------|
| **포함-배제 원리**(inclusion-exclusion principle) | 합집합의 원소 수를 구하는 공식 |
| **합집합**(union) | 두 집합 중 하나 이상에 속하는 원소들 |
| **교집합**(intersection) | 두 집합 모두에 속하는 원소들 |
| **벤 다이어그램**(Venn diagram) | 집합 관계를 시각화하는 도구 |
| **전사 함수**(surjection) | 공역의 모든 원소가 상에 포함 |
| **교란**(derangement) | 모든 원소가 원래 위치가 아닌 순열 |

>  **왜 포함-배제를 배울까?**  
> "여학생 또는 2학년인 학생은 몇 명인가?"와 같은 질문에서, 단순히 두 수를 더하면 **중복 계산**이 발생한다. 포함-배제 원리는 이 중복을 체계적으로 제거하는 공식이다. 이 원리는 확률, 조합론, 정수론 등 수학 전반에 걸쳐 폭넓게 사용된다.

---

## 1. 두 집합의 포함-배제: 직관적 이해

### 1.1 문제 상황

한 이산수학 반에 30명의 여학생과 50명의 2학년생이 있다. 이 반의 학생 중 "여학생이거나 2학년인" 학생은 몇 명인가?

처음 생각: 30 + 50 = 80명? → **틀렸다!** 왜냐하면 "여자 2학년"이 양쪽 모두에서 세어지기 때문이다.

만약 여자 2학년이 15명이라면:

```
여학생이거나 2학년인 학생 = 30 + 50 - 15 = 65명
```

이것이 바로 포함-배제 원리의 핵심이다!

### 1.2 두 집합의 포함-배제 공식

> **공식**: 두 유한집합 `A`와 `B`에 대해:
>
> $$|A \cup B| = |A| + |B| - |A \cap B|$$

**직관적 이해**:
1. 먼저 `A`의 원소를 모두 센다 → `|A|`
2. 다음 `B`의 원소를 모두 센다 → `|B|`
3. 하지만 `A ∩ B`에 속하는 원소는 **두 번** 세었으므로, 한 번 빼준다 → `-|A ∩ B|`

>  **비유**: 파티에 온 사람을 셀 때, "빨간 모자를 쓴 사람"과 "안경을 쓴 사람"을 각각 세면, "빨간 모자 + 안경"인 사람이 두 번 세어진다. 그래서 한 번 빼줘야 한다.

### 1.3 Lean 4로 형식화

Lean 4의 Mathlib에서는 `Finset`(유한 집합)에 대해 이 공식이 이미 증명되어 있다.

```lean
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Finset

-- 두 집합의 합집합 크기 공식
-- Mathlib에 이미 있는 정리:
#check Finset.card_union_add_card_inter
-- card_union_add_card_inter :
--   (s ∪ t).card + (s ∩ t).card = s.card + t.card

-- 이것을 변형하면:
-- (s ∪ t).card = s.card + t.card - (s ∩ t).card
```

#### Lean 4 기초: Finset 다루기

`Finset`은 **유한 집합**을 나타내는 Lean 4의 타입이다. `Set`(무한 집합도 가능)과 달리, `Finset`은 원소를 열거할 수 있고 크기를 셀 수 있다.

```lean
-- Finset 만들기
def A : Finset ℕ := {1, 2, 3, 4, 5}
def B : Finset ℕ := {3, 4, 5, 6, 7}

-- 기본 연산
#eval A ∪ B         -- {1, 2, 3, 4, 5, 6, 7}
#eval A ∩ B         -- {3, 4, 5}
#eval A.card        -- 5
#eval B.card        -- 5
#eval (A ∪ B).card  -- 7
#eval (A ∩ B).card  -- 3

-- 포함-배제 확인: 7 = 5 + 5 - 3 ✓
```

---

## 2. 예제로 이해하기

### 2.1 예제 1: 이산수학 반 (Rosen 예제 1)

> **문제**: 컴퓨터과학 전공자 25명, 수학 전공자 13명, 복수 전공자 8명이 있다. 컴퓨터과학 또는 수학을 전공하는 학생은 몇 명인가?

```lean
-- 집합 크기만으로 계산
def csStudents : ℕ := 25
def mathStudents : ℕ := 13
def bothStudents : ℕ := 8

-- 포함-배제 적용
def eitherStudents : ℕ := csStudents + mathStudents - bothStudents

#eval eitherStudents  -- 30

-- Lean 4 형식적 증명
example : 25 + 13 - 8 = 30 := by norm_num
```

### 2.2 예제 2: 7 또는 11로 나누어지는 수 (Rosen 예제 2)

> **문제**: 7 또는 11로 나누어지는 1000을 초과하지 않는 양의 정수는 몇 개인가?

풀이:
- `A` = 7로 나누어지는 수: `⌊1000/7⌋ = 142`개
- `B` = 11로 나누어지는 수: `⌊1000/11⌋ = 90`개
- `A ∩ B` = 7과 11 모두로 나누어지는 수 (= 77로 나누어지는 수): `⌊1000/77⌋ = 12`개

```lean
-- 직접 계산
#eval 1000 / 7    -- 142
#eval 1000 / 11   -- 90
#eval 1000 / 77   -- 12 (7 × 11 = 77)

-- 포함-배제
#eval 142 + 90 - 12  -- 220

-- Finset으로 정확한 검증
def divBy (d n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun k => k > 0 && k % d == 0)

#eval (divBy 7 1000).card   -- 142
#eval (divBy 11 1000).card  -- 90
#eval ((divBy 7 1000) ∩ (divBy 11 1000)).card  -- 12
#eval ((divBy 7 1000) ∪ (divBy 11 1000)).card  -- 220 ✓
```

### 2.3 예제 3: 세 과목 (Rosen 예제 3)

> **문제**: 1807명의 신입생 중 453명은 컴퓨터과학, 567명은 수학, 299명은 양쪽 모두를 수강한다. 컴퓨터과학 또는 수학을 수강하지 않는 학생은?

```lean
-- |A ∪ B| = 453 + 567 - 299 = 721
-- 수강하지 않는 학생 = 1807 - 721 = 1086

example : 1807 - (453 + 567 - 299) = 1086 := by norm_num
```

---

## 3. 세 집합의 포함-배제

### 3.1 공식

두 집합으로는 부족할 때가 많다. 세 집합 `A`, `B`, `C`의 합집합 크기는:

> $$|A \cup B \cup C| = |A| + |B| + |C| - |A \cap B| - |A \cap C| - |B \cap C| + |A \cap B \cap C|$$

**왜 이렇게 되는가?** 벤 다이어그램으로 생각해 보자:

1. `|A| + |B| + |C|`로 시작하면, **두 집합에만** 속하는 원소는 2번, **세 집합 모두**에 속하는 원소는 3번 세어진다.
2. `-|A ∩ B| - |A ∩ C| - |B ∩ C|`로 두 집합씩의 교집합을 빼면, 두 집합에만 속하는 원소는 정확히 1번, 세 집합 모두에 속하는 원소는 `3 - 3 = 0`번이 된다.
3. `+|A ∩ B ∩ C|`로 세 집합의 교집합을 다시 더하면, 세 집합 모두에 속하는 원소도 정확히 1번 세어진다.

>  **비유**: "더하고 → 빼고 → 다시 더하기"를 반복하면서, 모든 원소가 정확히 한 번만 세어지도록 조정하는 것이다!

### 3.2 예제 4: 세 언어 수강 (Rosen 예제 4)

> **문제**: 1232명은 스페인어, 879명은 프랑스어, 114명은 러시아어를 수강한다.  
> 스페인어∩프랑스어 = 103, 스페인어∩러시아어 = 23, 프랑스어∩러시아어 = 14  
> 세 언어 중 하나를 수강하는 학생이 2092명이면, 세 언어 모두를 수강하는 학생은?

```lean
-- |S ∪ F ∪ R| = |S| + |F| + |R| - |S∩F| - |S∩R| - |F∩R| + |S∩F∩R|
-- 2092 = 1232 + 879 + 114 - 103 - 23 - 14 + |S∩F∩R|
-- 2092 = 2085 + |S∩F∩R|
-- |S∩F∩R| = 7

example : 2092 = 1232 + 879 + 114 - 103 - 23 - 14 + 7 := by norm_num

-- 또는 역으로:
example : 1232 + 879 + 114 - 103 - 23 - 14 + 7 = 2092 := by norm_num
```

```lean
-- Lean 4 Finset으로 세 집합 포함-배제 증명
theorem inclusion_exclusion_three
    {α : Type*} [DecidableEq α]
    (A B C : Finset α) :
    (A ∪ B ∪ C).card =
      A.card + B.card + C.card
      - (A ∩ B).card - (A ∩ C).card - (B ∩ C).card
      + (A ∩ B ∩ C).card := by
  sorry  -- Mathlib의 card_union과 관련 보조정리들로 증명 가능
```

---

## 4. n개 집합의 포함-배제 원리 (정리 1)

### 4.1 일반화된 공식

> **정리 1** (포함-배제 원리):  
> `A₁, A₂, ..., Aₙ`이 유한집합이라 하자. 그러면:
>
> $$|A_1 \cup A_2 \cup \cdots \cup A_n| = \sum_{i} |A_i| - \sum_{i<j} |A_i \cap A_j| + \sum_{i<j<k} |A_i \cap A_j \cap A_k| - \cdots + (-1)^{n+1}|A_1 \cap A_2 \cap \cdots \cap A_n|$$

이 공식은 **교대 합**(alternating sum)의 형태이다:
- 홀수 개의 집합 교집합 → **더한다** (+)
- 짝수 개의 집합 교집합 → **뺀다** (-)

### 4.2 공식의 항 수

`n`개의 집합에 대한 포함-배제 공식에는 `2ⁿ - 1`개의 항이 있다. (공집합을 제외한 모든 부분집합에 대해 하나씩)

- `n = 2`: `2² - 1 = 3`개의 항 (`|A|, |B|, |A∩B|`)
- `n = 3`: `2³ - 1 = 7`개의 항
- `n = 4`: `2⁴ - 1 = 15`개의 항

### 4.3 증명의 핵심 아이디어

증명의 핵심은 "각 원소가 정확히 한 번만 세어진다"는 것이다.

어떤 원소 `a`가 정확히 `r`개의 집합에 속한다고 하자 (`1 ≤ r ≤ n`). 그러면 이 원소는 우변에서:

$$C(r, 1) - C(r, 2) + C(r, 3) - \cdots + (-1)^{r+1}C(r, r)$$

번 세어진다. 이항 정리에 의해 이 값은:

$$1 - [C(r, 0) - C(r, 1) + C(r, 2) - \cdots + (-1)^r C(r, r)] = 1 - (1 - 1)^r = 1 - 0 = 1$$

따라서 모든 원소가 정확히 한 번 세어진다! ∎

```lean
-- 증명의 핵심 보조정리: 교대 이항 합 = 0
-- C(r,0) - C(r,1) + C(r,2) - ... + (-1)^r * C(r,r) = 0 (r > 0)
theorem alternating_binom_sum (r : ℕ) (hr : r > 0) :
    (Finset.range (r + 1)).sum (fun k => (-1 : ℤ) ^ k * (Nat.choose r k : ℤ)) = 0 := by
  sorry  -- 이항 정리 (1 + (-1))^r = 0^r = 0

-- 구체적 검증
-- r = 1: C(1,0) - C(1,1) = 1 - 1 = 0 ✓
-- r = 2: C(2,0) - C(2,1) + C(2,2) = 1 - 2 + 1 = 0 ✓
-- r = 3: C(3,0) - C(3,1) + C(3,2) - C(3,3) = 1 - 3 + 3 - 1 = 0 ✓

example : (1 : ℤ) - 1 = 0 := by norm_num
example : (1 : ℤ) - 2 + 1 = 0 := by norm_num
example : (1 : ℤ) - 3 + 3 - 1 = 0 := by norm_num
```

---

## 5. 예제 5: 네 집합의 합집합 (Rosen 예제 5)

> **문제**: 네 집합의 합집합에 있는 원소의 수에 대한 공식을 제시하라.

포함-배제 원리에 의하면:

$$|A_1 \cup A_2 \cup A_3 \cup A_4| = |A_1| + |A_2| + |A_3| + |A_4|$$
$$- |A_1 \cap A_2| - |A_1 \cap A_3| - |A_1 \cap A_4| - |A_2 \cap A_3| - |A_2 \cap A_4| - |A_3 \cap A_4|$$
$$+ |A_1 \cap A_2 \cap A_3| + |A_1 \cap A_2 \cap A_4| + |A_1 \cap A_3 \cap A_4| + |A_2 \cap A_3 \cap A_4|$$
$$- |A_1 \cap A_2 \cap A_3 \cap A_4|$$

이 공식은 `{A₁, A₂, A₃, A₄}`의 공집합이 아닌 모든 부분집합에 대해 하나의 항을 가지며, 총 `2⁴ - 1 = 15`개의 항이 있다.

```lean
-- 네 집합의 포함-배제를 Lean 4로 직접 계산하는 예시
def S1 : Finset ℕ := {1, 2, 3, 4, 5, 6, 7, 8}
def S2 : Finset ℕ := {2, 4, 6, 8, 10, 12}
def S3 : Finset ℕ := {3, 6, 9, 12, 15}
def S4 : Finset ℕ := {5, 10, 15, 20}

-- 직접 합집합 계산
#eval (S1 ∪ S2 ∪ S3 ∪ S4).card  -- 15

-- 포함-배제로 계산
#eval S1.card + S2.card + S3.card + S4.card
    - (S1 ∩ S2).card - (S1 ∩ S3).card - (S1 ∩ S4).card
    - (S2 ∩ S3).card - (S2 ∩ S4).card - (S3 ∩ S4).card
    + (S1 ∩ S2 ∩ S3).card + (S1 ∩ S2 ∩ S4).card
    + (S1 ∩ S3 ∩ S4).card + (S2 ∩ S3 ∩ S4).card
    - (S1 ∩ S2 ∩ S3 ∩ S4).card
-- 15 ✓
```

---

## 6. 포함-배제의 다른 형식: "속성이 없는" 원소 세기

### 6.1 여사건으로의 변환 (Rosen 8.6절)

포함-배제를 사용할 때, 종종 "**속성 P₁, P₂, ..., Pₙ 중 어느 것도 갖지 않는** 원소의 수"를 구하고 싶을 때가 있다.

전체 집합의 크기를 `N`이라 하면:

> $$N(P_1'P_2' \cdots P_n') = N - |A_1 \cup A_2 \cup \cdots \cup A_n|$$

여기서 `Aᵢ`는 속성 `Pᵢ`를 가진 원소들의 집합이다.

포함-배제를 대입하면:

> $$N(P_1'P_2' \cdots P_n') = N - \sum |A_i| + \sum |A_i \cap A_j| - \cdots + (-1)^n |A_1 \cap \cdots \cap A_n|$$

### 6.2 응용: 오일러의 피 함수 (Euler's Totient Function)

`n`보다 작거나 같은 양의 정수 중 `n`과 서로소인 수의 개수를 **오일러의 피 함수**(Euler's totient function) `φ(n)`이라 한다.

포함-배제를 이용하면:
- `n = p₁^a₁ · p₂^a₂ · ... · pₖ^aₖ` (소인수 분해)일 때
- `φ(n) = n · (1 - 1/p₁)(1 - 1/p₂)···(1 - 1/pₖ)`

```lean
-- 오일러의 피 함수 직접 구현
def eulerPhi (n : ℕ) : ℕ :=
  if n ≤ 1 then n
  else (Finset.range n).filter (fun k => k > 0 && Nat.gcd k n == 1) |>.card

#eval eulerPhi 12   -- 4 (1, 5, 7, 11이 12와 서로소)
#eval eulerPhi 30   -- 8
#eval eulerPhi 7    -- 6 (소수이므로 1~6 모두)

-- 포함-배제로 φ(12) 계산
-- 12 = 2² × 3
-- 1~12 중 2의 배수: 6개, 3의 배수: 4개, 6의 배수: 2개
-- 2 또는 3의 배수: 6 + 4 - 2 = 8개
-- 서로소: 12 - 8 = 4 ✓
example : 12 - (6 + 4 - 2) = 4 := by norm_num
```

---

## 7. Lean 4에서의 포함-배제 상세 구현

### 7.1 두 집합 포함-배제 완전한 증명

```lean
-- Lean 4에서 두 집합의 포함-배제 증명
-- Mathlib의 정리를 직접 사용
theorem ie_two {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
  Finset.card_union_add_card_inter A B

-- 변형: |A ∪ B| = |A| + |B| - |A ∩ B|
-- 자연수 뺄셈 주의! 항상 |A ∩ B| ≤ |A| + |B|이므로 안전
theorem ie_two_sub {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∪ B).card = A.card + B.card - (A ∩ B).card := by
  have h := Finset.card_union_add_card_inter A B
  omega
```

### 7.2 `→`(if)와 `↔`(if and only if)의 차이

포함-배제 원리를 학습하면서, 논리 기호 `→`와 `↔`의 차이를 명확히 하자.

#### `→` (if, **조건문**)

`P → Q`는 "`P`이면 `Q`이다"를 뜻한다. **한 방향**만 성립한다.

- 예: `x ∈ A ∩ B → x ∈ A` (교집합에 속하면 A에 속한다)
- 역(`Q → P`)은 반드시 성립하지 않는다!

#### `↔` (if and only if, **쌍방향 조건문**)

`P ↔ Q`는 "`P`이면 `Q`이고 `Q`이면 `P`이다"를 뜻한다. **양 방향** 모두 성립한다.

- 예: `x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B` (합집합의 정의)
- `P ↔ Q`는 `(P → Q) ∧ (Q → P)`와 같다!

```lean
-- → (if): 한 방향
example {α : Type*} [DecidableEq α] {x : α} {A B : Finset α}
    (h : x ∈ A ∩ B) : x ∈ A := by
  exact Finset.mem_inter.mp h |>.1

-- ↔ (iff): 양 방향
example {α : Type*} [DecidableEq α] {x : α} {A B : Finset α} :
    x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B :=
  Finset.mem_union

-- ↔를 → 두 개로 분해
example {P Q : Prop} (h : P ↔ Q) : P → Q := h.mp
example {P Q : Prop} (h : P ↔ Q) : Q → P := h.mpr

-- Lean 4에서 ↔ 증명하기
example {P Q : Prop} (hpq : P → Q) (hqp : Q → P) : P ↔ Q :=
  ⟨hpq, hqp⟩
```

### 7.3 lemma(작은 정리)와 theorem(큰 정리)의 관계

Lean 4에서 `lemma`와 `theorem`은 **기능적으로 동일**하다! 둘 다 명제의 증명을 나타낸다. 차이는 **관례**(convention)에 있다:

| 구분 | `lemma` | `theorem` |
|------|---------|-----------|
| **역할** | 큰 정리를 증명하기 위한 **보조 단계** | 그 자체로 중요한 **주요 결과** |
| **비유** | 건물의 **벽돌**  | 완성된 **건물**  |
| **수학에서** | "보조 정리" (auxiliary result) | "정리" (main result) |
| **Lean 4에서** | `lemma foo : ...` | `theorem bar : ...` |

```lean
-- lemma: 포함-배제를 증명하기 위한 보조 단계
lemma inter_subset_union {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∩ B) ⊆ (A ∪ B) := by
  intro x hx
  exact Finset.mem_union_left B (Finset.mem_inter.mp hx |>.1)

-- theorem: 포함-배제 원리 자체 (이 lemma를 사용)
theorem inclusion_exclusion_card {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∪ B).card = A.card + B.card - (A ∩ B).card := by
  have h := Finset.card_union_add_card_inter A B
  omega
```

> 💡 **요약**: `lemma`는 벽돌, `theorem`은 건물이다. 실제로 Lean 4 컴파일러는 이 둘을 구분하지 않지만, 인간 독자를 위해 구분하는 것이 좋은 습관이다.

---

## 8. 치환/대입 = 슈퍼포지션 (Substitution = Superposition)

### 8.1 치환이란?

**치환**(substitution) 또는 **대입**이란, 수식에서 변수를 다른 식으로 바꾸는 것이다. Lean 4에서는 `rw` (rewrite) 전술이 이 역할을 한다.

>  **비유**: 레시피에서 "밀가루"를 "쌀가루"로 바꾸는 것과 같다. 레시피의 구조는 같지만, 재료가 바뀐다.

### 8.2 Lean 4에서의 치환: `rw` 전술

```lean
-- 기본 치환 예시
-- h : a = b 가 있을 때, 목표에서 a를 b로 바꾼다
example (a b c : ℕ) (h : a = b) : a + c = b + c := by
  rw [h]  -- a를 b로 치환

-- 여러 번 치환
example (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]  -- a → b
  rw [h2]  -- b → c (또는 exact h2)

-- 역방향 치환: rw [← h]
example (a b : ℕ) (h : a = b) : b = a := by
  rw [← h]  -- b → a (역방향)
```

### 8.3 슈퍼포지션과의 관계

**슈퍼포지션**(superposition)은 자동 정리 증명에서 사용하는 용어로, 두 식을 **통합**(unification)하여 하나의 새로운 식을 만드는 과정이다. 본질적으로 치환과 같은 아이디어이다:

1. **치환**(substitution): "이 변수를 저 식으로 바꿔라"
2. **슈퍼포지션**(superposition): "두 등식을 결합하여 새 등식을 유도하라"

```lean
-- 슈퍼포지션의 예: 두 등식을 결합
-- h1: f(a) = g(b)
-- h2: g(b) = c
-- 결론: f(a) = c (h1과 h2를 "합성")

example (f g : ℕ → ℕ) (a b c : ℕ)
    (h1 : f a = g b) (h2 : g b = c) : f a = c := by
  rw [h1, h2]  -- 치환 두 번 = 슈퍼포지션 한 번

-- calc 블록으로도 같은 것을 표현
example (f g : ℕ → ℕ) (a b c : ℕ)
    (h1 : f a = g b) (h2 : g b = c) : f a = c :=
  calc f a = g b := h1
    _ = c := h2
```

---

## 9. 연습 문제

### 연습 9.1: 두 집합 포함-배제 [괄호 채우기]

> 대학에서 345명이 미적분학, 212명이 이산수학, 188명이 두 과목 모두를 수강했다. 미적분학 또는 이산수학을 수강한 학생은?

```lean
-- |A ∪ B| = |A| + |B| - |A ∩ B|
-- = 345 + 212 - 188
-- = (     )

example : 345 + 212 - 188 = (  sorry  ) := by norm_num
```

<details>
<summary> 답 보기</summary>

```lean
example : 345 + 212 - 188 = 369 := by norm_num
```

</details>

---

### 연습 9.2: 세 집합 포함-배제 [괄호 채우기]

> 각 집합에 100개의 원소가 있고, 집합들의 각 쌍이 50개의 공통 원소를 갖고, 세 집합 모두에 25개의 원소가 있을 때, `|A₁ ∪ A₂ ∪ A₃|`을 구하라.

```lean
-- |A₁ ∪ A₂ ∪ A₃| = |A₁| + |A₂| + |A₃| - |A₁∩A₂| - |A₁∩A₃| - |A₂∩A₃| + |A₁∩A₂∩A₃|
-- = 100 + 100 + 100 - 50 - 50 - 50 + 25
-- = (     )

example : 100 + 100 + 100 - 50 - 50 - 50 + 25 = (  sorry  ) := by norm_num
```

<details>
<summary> 답 보기</summary>

```lean
example : 100 + 100 + 100 - 50 - 50 - 50 + 25 = 175 := by norm_num
```

</details>

---

### 연습 9.3: Finset 포함-배제 [괄호 채우기]

> Lean 4 Finset을 사용하여 구체적인 집합의 포함-배제를 확인하라.

```lean
def X : Finset ℕ := {1, 2, 3, 4, 5, 6}
def Y : Finset ℕ := {4, 5, 6, 7, 8, 9}

-- X.card = (     )
-- Y.card = (     )
-- (X ∩ Y).card = (     )
-- (X ∪ Y).card = (     )
-- X.card + Y.card - (X ∩ Y).card = (     )

#eval X.card
#eval Y.card
#eval (X ∩ Y).card
#eval (X ∪ Y).card
```

<details>
<summary> 답 보기</summary>

```
X.card = 6
Y.card = 6
(X ∩ Y).card = 3  -- {4, 5, 6}
(X ∪ Y).card = 9  -- {1, 2, 3, 4, 5, 6, 7, 8, 9}
6 + 6 - 3 = 9 ✓
```

</details>

---

### 연습 9.4: → 와 ↔ 구분 [괄호 채우기]

> 다음 중 `→`만 성립하는 것과 `↔`가 성립하는 것을 구분하라.

```lean
-- (1) x ∈ A ∩ B (     ) x ∈ A    -- → 또는 ↔ ?
-- (2) x ∈ A ∪ B (     ) x ∈ A ∨ x ∈ B  -- → 또는 ↔ ?
-- (3) A ⊆ B (     ) A ∪ B = B    -- → 또는 ↔ ?
```

<details>
<summary> 답 보기</summary>

1. `→` (한 방향만): `x ∈ A ∩ B → x ∈ A`는 성립하지만, 역은 아니다 (x가 B에 없을 수 있다)
2. `↔` (양방향): 합집합의 **정의** 자체이다
3. `↔` (양방향): `A ⊆ B ↔ A ∪ B = B`는 양방향 모두 성립한다

</details>

---

### 연습 9.5: lemma와 theorem 연습 [Skeleton]

> 다음 코드에서 `lemma`를 먼저 증명한 후, 이를 사용하여 `theorem`을 증명하라.

```lean
-- 보조 정리: 교집합은 각 집합의 부분집합
lemma inter_subset_left' {α : Type*} [DecidableEq α] (A B : Finset α) :
    A ∩ B ⊆ A := by
  sorry

-- 보조 정리: 부분집합이면 크기가 작거나 같다
lemma card_le_of_subset' {α : Type*} [DecidableEq α] {s t : Finset α}
    (h : s ⊆ t) : s.card ≤ t.card := by
  sorry

-- 주 정리: 교집합의 크기 ≤ 각 집합의 크기
theorem inter_card_le {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∩ B).card ≤ A.card := by
  sorry  -- 위 두 lemma를 사용
```

<details>
<summary>💡 답 보기</summary>

```lean
lemma inter_subset_left' {α : Type*} [DecidableEq α] (A B : Finset α) :
    A ∩ B ⊆ A :=
  Finset.inter_subset_left

lemma card_le_of_subset' {α : Type*} [DecidableEq α] {s t : Finset α}
    (h : s ⊆ t) : s.card ≤ t.card :=
  Finset.card_le_card h

theorem inter_card_le {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∩ B).card ≤ A.card :=
  card_le_of_subset' (inter_subset_left' A B)
```

</details>

---

### 연습 9.6: 3, 17, 35로 나누어지는 수 [Sorry 도전]

> 1000을 넘지 않으면서 3, 17 또는 35로 나누어지는 양의 정수의 수를 구하라.

```lean
-- 힌트: 3과 17은 서로소, 3과 35는 공약수 ≠ 1 (둘다 1을 제외하면 없음... 아 잠깐)
-- 3과 35의 최소공배수 = 105, 17과 35의 최소공배수 = 595
-- 3과 17의 최소공배수 = 51
-- 3, 17, 35의 최소공배수 = lcm(51, 35) = 1785

-- Finset으로 정확한 답 구하기
def divByAny (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun k =>
    k > 0 && (k % 3 == 0 || k % 17 == 0 || k % 35 == 0))

-- #eval (divByAny 1000).card  -- 정답은?

theorem divisible_count : (divByAny 1000).card = sorry := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
-- |A| = ⌊1000/3⌋ = 333
-- |B| = ⌊1000/17⌋ = 58
-- |C| = ⌊1000/35⌋ = 28
-- |A∩B| = ⌊1000/51⌋ = 19  (lcm(3,17) = 51)
-- |A∩C| = ⌊1000/105⌋ = 9  (lcm(3,35) = 105)
-- |B∩C| = ⌊1000/595⌋ = 1  (lcm(17,35) = 595)
-- |A∩B∩C| = ⌊1000/1785⌋ = 0  (lcm(3,17,35) = 1785)
--
-- |A∪B∪C| = 333 + 58 + 28 - 19 - 9 - 1 + 0 = 390

#eval (divByAny 1000).card  -- 390

theorem divisible_count : (divByAny 1000).card = 390 := by native_decide
```

</details>

---

### 연습 9.7: 오일러 피 함수 [Sorry 도전]

> `φ(30)`을 포함-배제를 이용하여 계산하고, Lean 4로 검증하라.

```lean
-- 30 = 2 × 3 × 5
-- 1~30 중:
--   2의 배수: 15개, 3의 배수: 10개, 5의 배수: 6개
--   6의 배수: 5개, 10의 배수: 3개, 15의 배수: 2개
--   30의 배수: 1개
-- 2, 3, 또는 5의 배수: 15 + 10 + 6 - 5 - 3 - 2 + 1 = 22
-- φ(30) = 30 - 22 = 8

theorem euler_phi_30 : eulerPhi 30 = 8 := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
theorem euler_phi_30 : eulerPhi 30 = 8 := by native_decide
```

</details>

---

### 연습 9.8: 교대 이항 합 [Sorry 도전]

> `r = 4`일 때 `C(4,0) - C(4,1) + C(4,2) - C(4,3) + C(4,4) = 0`을 Lean 4로 증명하라.

```lean
-- C(4,0) - C(4,1) + C(4,2) - C(4,3) + C(4,4)
-- = 1 - 4 + 6 - 4 + 1 = 0

theorem alt_binom_sum_4 :
    (1 : ℤ) - 4 + 6 - 4 + 1 = 0 := by
  sorry

-- Nat.choose 버전
theorem alt_binom_sum_4' :
    (Nat.choose 4 0 : ℤ) - (Nat.choose 4 1 : ℤ) + (Nat.choose 4 2 : ℤ)
    - (Nat.choose 4 3 : ℤ) + (Nat.choose 4 4 : ℤ) = 0 := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
theorem alt_binom_sum_4 :
    (1 : ℤ) - 4 + 6 - 4 + 1 = 0 := by norm_num

theorem alt_binom_sum_4' :
    (Nat.choose 4 0 : ℤ) - (Nat.choose 4 1 : ℤ) + (Nat.choose 4 2 : ℤ)
    - (Nat.choose 4 3 : ℤ) + (Nat.choose 4 4 : ℤ) = 0 := by native_decide
```

</details>

---

### 연습 9.9: rw 치환 연습 [Skeleton]

> `rw` 전술을 사용하여 다음을 증명하라.

```lean
-- (1) 간단한 치환
example (a b c : ℕ) (h1 : a = b + 1) (h2 : c = a + 2) : c = b + 3 := by
  sorry

-- (2) 역방향 치환
example (x y : ℕ) (h : x + y = 10) : 10 = x + y := by
  sorry

-- (3) 연쇄 치환
example (a b c d : ℕ) (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
example (a b c : ℕ) (h1 : a = b + 1) (h2 : c = a + 2) : c = b + 3 := by
  rw [h2, h1]; ring

example (x y : ℕ) (h : x + y = 10) : 10 = x + y := by
  rw [← h]  -- 또는 omega / exact h.symm

example (a b c d : ℕ) (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by
  rw [h1, h2, h3]
```

</details>

---

### 연습 9.10: 종합 문제 [Sorry 도전]

> **문제**: 270명의 대학생에 대해:
> - 브뤼셀 스프라우트를 좋아하는 학생: 64명
> - 브로콜리를 좋아하는 학생: 94명
> - 컬리플라워를 좋아하는 학생: 58명
> - 브뤼셀 스프라우트와 브로콜리 모두: 26명
> - 브뤼셀 스프라우트와 컬리플라워 모두: 28명
> - 브로콜리와 컬리플라워 모두: 22명
> - 세 가지 모두: 14명
>
> 어떤 채소도 좋아하지 않는 학생은?

```lean
-- |A∪B∪C| = 64 + 94 + 58 - 26 - 28 - 22 + 14 = ?
-- 좋아하지 않는 학생 = 270 - |A∪B∪C| = ?

theorem vegetable_problem :
    270 - (64 + 94 + 58 - 26 - 28 - 22 + 14) = sorry := by
  sorry
```

<details>
<summary> 답 보기</summary>

```lean
-- |A∪B∪C| = 64 + 94 + 58 - 26 - 28 - 22 + 14 = 154
-- 좋아하지 않는 학생 = 270 - 154 = 116

theorem vegetable_problem :
    270 - (64 + 94 + 58 - 26 - 28 - 22 + 14) = 116 := by norm_num
```

</details>

---

## 10. 사용된 Lean 4 전술 · 함수 정리

### 전술 요약

| 전술 | 용도 | 예시 |
|------|------|------|
| `rw [h]` | `h : a = b`로 목표의 `a`를 `b`로 치환 | `rw [h1, h2]` |
| `rw [← h]` | 역방향 치환 (`b`를 `a`로) | `rw [← h]` |
| `norm_num` | 수치 계산 자동 증명 | `100 - 50 = 50` |
| `native_decide` | 결정 가능한 명제 자동 증명 | `Finset.card` 계산 |
| `omega` | 자연수/정수 선형 부등식 | `a + b - c = d` |
| `exact` | 증명 항 직접 제공 | `exact h.mp` |

### 개념 요약

| 개념 | Lean 4 | 설명 |
|------|--------|------|
| 합집합 | `A ∪ B` | `Finset.union` |
| 교집합 | `A ∩ B` | `Finset.inter` |
| 크기 | `A.card` | `Finset.card` |
| 부분집합 | `A ⊆ B` | `Finset.Subset` |
| 필터 | `s.filter p` | 조건 만족하는 원소만 |
| 범위 | `Finset.range n` | `{0, 1, ..., n-1}` |

---

## 11. 핵심 요약

1. **포함-배제 원리**는 합집합의 크기를 계산할 때, 중복 계산을 체계적으로 제거하는 공식이다.
2. 두 집합: `|A ∪ B| = |A| + |B| - |A ∩ B|`
3. 세 집합: `|A∪B∪C| = |A|+|B|+|C| - |A∩B|-|A∩C|-|B∩C| + |A∩B∩C|`
4. 일반 `n`개: "더하고 → 빼고"를 교대로 반복하며, 각 원소가 정확히 1번 세어진다.
5. **`→`(if)** 는 한 방향, **`↔`(iff)** 는 양 방향의 논리적 관계이다.
6. **`lemma`** 는 큰 정리를 위한 벽돌, **`theorem`** 은 완성된 건물이다. Lean 4에서 기능은 동일하다.
7. **치환**(substitution) = Lean 4의 `rw` 전술. 등식을 이용해 식의 일부를 교체하는 핵심 도구이다.
8. 포함-배제의 응용: **오일러 피 함수**, 전사 함수의 수, 교란(derangement) 문제 등.

---

> **다음 파트 예고**: Part 11-E에서는 **포함-배제의 고급 응용**(Rosen 8.6절 나머지)을 다룬다. 전사 함수의 수를 구하는 공식, **교란**(derangement, 완전순열) 문제, 그리고 이를 Lean 4로 형식화하는 방법을 배운다!
