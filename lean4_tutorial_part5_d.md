# Lean4 완전 정복 가이드 — 제5-d편

## 집합의 크기와 행렬 완전 정복

> **교재**: Kenneth H. Rosen, "Discrete Mathematics and Its Applications" 8판  
> **범위**: 2.5절 집합의 크기, 2.6절 행렬  
> **선수 학습**: 제5-c편 (수열과 수열의 합)

---

## 목차

- [5-d.1 서론: 무한을 세다](#5-d1-서론-무한을-세다)
- [5-d.2 집합의 크기와 전단사 함수](#5-d2-집합의-크기와-전단사-함수)
- [5-d.3 셀 수 있는 집합](#5-d3-셀-수-있는-집합)
- [5-d.4 힐버트 호텔 역설](#5-d4-힐버트-호텔-역설)
- [5-d.5 칸토르 대각선 논증](#5-d5-칸토르-대각선-논증)
- [5-d.6 Lean4에서 집합의 크기](#5-d6-lean4에서-집합의-크기)
- [5-d.7 행렬의 정의](#5-d7-행렬의-정의)
- [5-d.8 Lean4에서 행렬 표현](#5-d8-lean4에서-행렬-표현)
- [5-d.9 행렬의 연산](#5-d9-행렬의-연산)
- [5-d.10 전치행렬과 대칭행렬](#5-d10-전치행렬과-대칭행렬)
- [5-d.11 0-1 행렬과 부울 곱](#5-d11-0-1-행렬과-부울-곱)
- [5-d.12 연습문제](#5-d12-연습문제)
- [5-d.13 도전 문제](#5-d13-도전-문제)
- [5-d.14 전술 요약](#5-d14-전술-요약)

---

## 5-d.1 서론: 무한을 세다

### 5-d.1.1 일상의 "크기" 개념

일상에서 집합의 크기를 비교하는 것은 직관적이다:

- **사과 5개** vs **배 3개** → 사과가 더 많다
- **학생 30명** vs **책상 30개** → 같은 수이다

유한 집합에서는 "원소를 하나씩 세면" 크기를 알 수 있다.

### 5-d.1.2 무한 집합의 수수께끼

그러나 무한 집합에서는 이상한 일이 벌어진다:

| 질문 | 직관적 답 | 실제 답 |
|------|---------|---------|
| 자연수와 짝수 중 어느 쪽이 더 많을까? | 자연수가 2배 많다 | **같다** |
| 정수와 자연수 중 어느 쪽이 더 많을까? | 정수가 2배 많다 | **같다** |
| 실수와 자연수 중 어느 쪽이 더 많을까? | 실수가 더 많다 | **실수가 더 많다** |

어떻게 무한한 것들의 "크기"를 비교할 수 있을까? 이 질문에 답한 사람이 바로 **게오르크 칸토르**(Georg Cantor, 1845-1918)이다.

### 5-d.1.3 이 장에서 배울 내용

| 개념 | 설명 |
|------|------|
| **기수**(cardinality) | 집합의 "크기" |
| **전단사 함수**(bijection) | 두 집합의 크기가 같음을 보이는 도구 |
| **셀 수 있음**(countable) | 자연수로 번호를 붙일 수 있음 |
| **셀 수 없음**(uncountable) | 자연수로 번호를 붙일 수 없음 |
| **대각선 논증** | 셀 수 없음을 증명하는 방법 |

---

## 5-d.2 집합의 크기와 전단사 함수

### 5-d.2.1 기수의 정의

**정의 1** (Rosen 2.5절):

> 집합 A와 B가 **같은 기수**(same cardinality)를 가진다는 것은 A에서 B로의 **전단사 함수**(일대일 대응)가 존재한다는 것이다.

기호로 |A| = |B|라고 쓴다.

### 5-d.2.2 전단사 함수 복습

**전단사 함수**(bijection)란:
- **단사**(injective, one-to-one): 서로 다른 입력은 서로 다른 출력
- **전사**(surjective, onto): 모든 출력이 어떤 입력의 상(image)

```lean
-- 단사 함수의 정의
def injective (f : α → β) : Prop :=
  ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂

-- 전사 함수의 정의  
def surjective (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b

-- 전단사 함수의 정의
def bijective (f : α → β) : Prop :=
  injective f ∧ surjective f
```

### 5-d.2.3 유한 집합의 크기 비교

**예제 1**: {a, b, c}와 {1, 2, 3}의 크기가 같음을 보이기

```lean
-- 전단사 함수 정의
def f : Fin 3 → Fin 3 := fun n => n  -- 항등 함수

-- 이 함수가 전단사임을 증명
example : Function.Bijective f := by
  constructor
  · -- 단사 증명
    intro x y hxy
    exact hxy
  · -- 전사 증명
    intro y
    use y
    rfl
```

### 5-d.2.4 무한 집합의 크기 비교

**예제 2**: 자연수 ℕ와 짝수 집합 {0, 2, 4, 6, ...}의 크기가 같다

전단사 함수: f(n) = 2n

```
n  : 0  1  2  3  4  5  ...
2n : 0  2  4  6  8  10 ...
```

이 함수는:
- **단사**: 2n₁ = 2n₂ → n₁ = n₂
- **전사**: 모든 짝수 2k에 대해 f(k) = 2k

```lean
-- 자연수에서 짝수로의 함수
def doubling : Nat → Nat := fun n => 2 * n

-- 단사 증명
theorem doubling_injective : Function.Injective doubling := by
  intro a b hab
  -- hab : 2 * a = 2 * b
  omega

-- 주의: 이 함수는 Nat → Nat 전체로는 전사가 아님
-- (1, 3, 5, ... 는 상(image)에 없음)
-- 하지만 "짝수 집합"으로의 함수로 보면 전사임
```

---

## 5-d.3 셀 수 있는 집합

### 5-d.3.1 정의

**정의 2** (Rosen 2.5절):

> 집합 A가 **셀 수 있다**(countable)는 것은:
> 1. A가 유한이거나, 또는
> 2. A와 자연수 집합 ℕ 사이에 전단사 함수가 존재한다

자연수와 전단사 함수가 존재하는 무한 집합을 **가산무한**(countably infinite)이라 한다.

### 5-d.3.2 셀 수 있는 집합의 예

**예제 3**: 홀수 집합 {1, 3, 5, 7, ...}은 셀 수 있다

전단사 함수: f(n) = 2n + 1

```
n    : 0  1  2  3  4  5  ...
2n+1 : 1  3  5  7  9  11 ...
```

```lean
-- 홀수 생성 함수
def oddNumber : Nat → Nat := fun n => 2 * n + 1

-- 처음 몇 개의 홀수
#eval oddNumber 0    -- 1
#eval oddNumber 1    -- 3
#eval oddNumber 2    -- 5
#eval oddNumber 3    -- 7

-- 단사 증명
theorem oddNumber_injective : Function.Injective oddNumber := by
  intro a b hab
  -- hab : 2 * a + 1 = 2 * b + 1
  omega
```

**예제 4**: 정수 집합 ℤ는 셀 수 있다

전단사 함수를 구성하는 방법:

```
n  : 0   1   2   3   4   5   6   7   ...
f(n): 0  -1   1  -2   2  -3   3  -4  ...
```

규칙:
- n이 0이면 → 0
- n이 홀수면 → -(n+1)/2
- n이 짝수(0 제외)면 → n/2

```lean
-- 자연수에서 정수로의 함수
def natToInt : Nat → Int
  | 0 => 0
  | n + 1 => if n % 2 = 0 
             then -(Int.ofNat (n / 2 + 1))
             else Int.ofNat ((n + 1) / 2)

-- 확인
#eval natToInt 0   -- 0
#eval natToInt 1   -- -1
#eval natToInt 2   -- 1
#eval natToInt 3   -- -2
#eval natToInt 4   -- 2
```

### 5-d.3.3 셀 수 있는 집합의 성질

**정리 1**: 셀 수 있는 집합의 부분집합은 셀 수 있다.

**정리 2**: 두 셀 수 있는 집합의 합집합은 셀 수 있다.

**정리 3**: 유한 개의 셀 수 있는 집합의 합집합은 셀 수 있다.

**정리 4**: 양의 유리수 집합 ℚ⁺는 셀 수 있다.

---

## 5-d.4 힐버트 호텔 역설

### 5-d.4.1 무한 호텔

**힐버트 호텔**(Hilbert's Grand Hotel)은 무한히 많은 방이 있는 호텔이다:

```
방 번호: 1, 2, 3, 4, 5, 6, 7, 8, ...
```

### 5-d.4.2 역설 1: 모든 방이 찼는데 새 손님이 온다면?

**상황**: 모든 방(무한히 많은)에 손님이 있다. 새로운 손님 1명이 도착했다.

**해결책**: 모든 기존 손님을 한 칸씩 옮긴다!

```
기존:  손님1→방1, 손님2→방2, 손님3→방3, ...
새로운: 새손님→방1, 손님1→방2, 손님2→방3, ...
```

```lean
-- 방 배정 함수: n번 손님 → (n+1)번 방
def shiftRoom : Nat → Nat := fun n => n + 1

-- 새 손님은 1번 방
-- 기존 손님들은 shift

-- 이것이 가능한 이유: ℕ와 ℕ∪{0}의 기수가 같기 때문
```

### 5-d.4.3 역설 2: 무한 버스가 도착한다면?

**상황**: 모든 방에 손님이 있는데, 무한히 많은 새 손님을 태운 버스가 도착했다.

**해결책**: 모든 기존 손님을 짝수 번 방으로 옮기고, 새 손님들은 홀수 번 방에 배정한다!

```
기존 손님: n번 손님 → 2n번 방
새 손님: n번 버스 손님 → (2n+1)번 방
```

```lean
-- 기존 손님 배정
def existingGuest : Nat → Nat := fun n => 2 * n

-- 새 손님 배정
def newGuest : Nat → Nat := fun n => 2 * n + 1

-- 모든 방이 정확히 한 명씩 배정됨
#eval existingGuest 1  -- 2 (기존 1번 손님 → 2번 방)
#eval existingGuest 2  -- 4 (기존 2번 손님 → 4번 방)
#eval newGuest 0       -- 1 (새 버스 0번 손님 → 1번 방)
#eval newGuest 1       -- 3 (새 버스 1번 손님 → 3번 방)
```

### 5-d.4.4 역설의 교훈

힐버트 호텔 역설이 보여주는 것:

| 유한 vs 무한 |
|-------------|
| 유한 집합: 일부 = 전체는 **불가능** |
| 무한 집합: 일부 = 전체가 **가능** |

무한 집합의 정의: 자기 자신의 진부분집합과 전단사 함수가 존재하는 집합

---

## 5-d.5 칸토르 대각선 논증

### 5-d.5.1 칸토르의 질문

칸토르는 물었다: "실수 집합 ℝ도 셀 수 있을까?"

답: **아니다!** 실수는 셀 수 없다.

### 5-d.5.2 대각선 논증의 핵심 아이디어

**증명 전략** (귀류법):

1. "실수가 셀 수 있다"고 가정한다
2. 그러면 모든 실수를 자연수로 번호 매길 수 있다: r₁, r₂, r₃, ...
3. 이 목록에 **없는** 실수를 만들어낸다 → 모순!

### 5-d.5.3 대각선 논증 상세

구간 (0, 1) 안의 실수만 고려하자. 모든 실수를 나열했다고 가정:

```
r₁ = 0.d₁₁ d₁₂ d₁₃ d₁₄ ...
r₂ = 0.d₂₁ d₂₂ d₂₃ d₂₄ ...
r₃ = 0.d₃₁ d₃₂ d₃₃ d₃₄ ...
r₄ = 0.d₄₁ d₄₂ d₄₃ d₄₄ ...
...
```

여기서 dᵢⱼ는 rᵢ의 소수점 아래 j번째 자리 숫자이다.

**대각선 숫자 구성**:

새로운 실수 x = 0.e₁e₂e₃e₄...를 다음과 같이 정의:

```
eᵢ = { 1  만약 dᵢᵢ ≠ 1
     { 2  만약 dᵢᵢ = 1
```

즉, **대각선** d₁₁, d₂₂, d₃₃, ... 의 각 숫자와 **다른** 숫자를 선택한다.

### 5-d.5.4 왜 x는 목록에 없는가?

- x ≠ r₁ (첫 번째 자리가 다름)
- x ≠ r₂ (두 번째 자리가 다름)  
- x ≠ r₃ (세 번째 자리가 다름)
- ...
- x ≠ rₙ (n번째 자리가 다름)

따라서 x는 목록의 **어떤 실수와도 다르다**!

### 5-d.5.5 결론

- 가정: 모든 실수를 나열했다
- 결론: 목록에 없는 실수 x를 찾았다
- 모순!

따라서 **실수는 셀 수 없다**.

### 5-d.5.6 Lean4에서의 표현

```lean
-- 칸토르 정리의 일반화된 형태:
-- 어떤 집합 A에서 A의 멱집합 P(A)로의 전사함수는 존재하지 않는다

-- 이것은 Mathlib에서 다음과 같이 증명되어 있다:
-- theorem cantor_surjective (f : α → Set α) : ¬Function.Surjective f

-- 아이디어: S = {x | x ∉ f(x)} 를 고려
-- 만약 f가 전사라면, ∃a, f(a) = S
-- 그러면 a ∈ S ↔ a ∉ f(a) = S → 모순!
```

```lean
-- 칸토르 정리 증명 (간단한 버전)
theorem cantor : ∀ f : α → Set α, ¬Function.Surjective f := by
  intro f hsurj
  -- S = {x | x ∉ f x} 를 정의
  let S : Set α := {x | x ∉ f x}
  -- f가 전사이므로 ∃a, f a = S
  obtain ⟨a, ha⟩ := hsurj S
  -- a ∈ S인지 아닌지 분석
  by_cases h : a ∈ S
  · -- a ∈ S인 경우
    -- S의 정의에 의해 a ∉ f a
    -- 그런데 f a = S이므로 a ∉ S → 모순
    have : a ∉ f a := h
    rw [ha] at this
    exact this h
  · -- a ∉ S인 경우
    -- a ∉ S이므로, S의 정의에 의해 ¬(a ∉ f a), 즉 a ∈ f a
    -- 그런데 f a = S이므로 a ∈ S → 모순
    have : a ∈ f a := by
      simp only [Set.mem_setOf_eq] at h
      push_neg at h
      exact h
    rw [ha] at this
    exact h this
```

---

## 5-d.6 Lean4에서 집합의 크기

### 5-d.6.1 유한 집합의 크기: Finset.card

Lean4에서 **유한 집합**(Finset)의 크기는 `Finset.card`로 계산한다:

```lean
import Mathlib.Data.Finset.Card

open Finset

-- range n = {0, 1, 2, ..., n-1}
#eval (range 5).card    -- 5
#eval (range 10).card   -- 10
#eval (range 0).card    -- 0

-- 명시적 집합의 크기
#eval ({1, 2, 3, 4, 5} : Finset Nat).card  -- 5
```

### 5-d.6.2 Fintype의 크기: Fintype.card

**유한 타입**(Fintype)은 원소가 유한 개인 타입이다:

```lean
import Mathlib.Data.Fintype.Card

-- Fin n = {0, 1, ..., n-1}
#eval Fintype.card (Fin 5)   -- 5
#eval Fintype.card (Fin 10)  -- 10

-- Bool = {true, false}
#eval Fintype.card Bool      -- 2

-- Unit = {()}
#eval Fintype.card Unit      -- 1
```

### 5-d.6.3 크기 관련 정리들

```lean
import Mathlib.Data.Finset.Card

open Finset

-- 공집합의 크기
example : (∅ : Finset Nat).card = 0 := card_empty

-- 합집합의 크기 (서로소인 경우)
-- |A ∪ B| = |A| + |B| (A ∩ B = ∅일 때)
example (A B : Finset Nat) (h : Disjoint A B) :
    (A ∪ B).card = A.card + B.card := card_union_of_disjoint h

-- 포함-배제 원리
-- |A ∪ B| = |A| + |B| - |A ∩ B|
example (A B : Finset Nat) :
    (A ∪ B).card = A.card + B.card - (A ∩ B).card := card_union_inter A B
```

### 5-d.6.4 크기 연습

```lean
-- range의 크기
example : (range 6).card = 6 := by native_decide

-- 구체적 집합의 크기
example : ({1, 2, 3, 4, 5} : Finset Nat).card = 5 := by native_decide

-- Fin n의 크기
example : Fintype.card (Fin 7) = 7 := by native_decide
```

---

## 5-d.7 행렬의 정의

### 5-d.7.1 행렬이란?

**정의 3** (Rosen 2.6절):

> **행렬**(matrix)은 수 또는 다른 원소들의 **직사각형 배열**이다.

m행 n열을 가진 행렬을 **m × n 행렬**이라 한다.

### 5-d.7.2 행렬의 표기법

m × n 행렬 A:

```
    열1   열2   열3   ...   열n
행1 [ a₁₁  a₁₂  a₁₃  ...  a₁ₙ ]
행2 [ a₂₁  a₂₂  a₂₃  ...  a₂ₙ ]
행3 [ a₃₁  a₃₂  a₃₃  ...  a₃ₙ ]
...   ...  ...  ...  ...  ...
행m [ aₘ₁  aₘ₂  aₘ₃  ...  aₘₙ ]
```

- **aᵢⱼ**: i행 j열의 원소 (행 먼저, 열 나중)
- **A = [aᵢⱼ]**: 행렬 A를 원소 aᵢⱼ로 표시

### 5-d.7.3 특수한 행렬들

| 이름 | 정의 | 예시 |
|------|------|------|
| **정사각 행렬** | m = n인 행렬 | 2×2, 3×3 행렬 |
| **행 벡터** | m = 1인 행렬 (1×n) | [1 2 3] |
| **열 벡터** | n = 1인 행렬 (m×1) | [1; 2; 3] |
| **영행렬** | 모든 원소가 0 | O |
| **단위행렬** | 대각선만 1, 나머지 0 | I |

### 5-d.7.4 단위행렬의 예

3 × 3 단위행렬:

```
    [ 1  0  0 ]
I = [ 0  1  0 ]
    [ 0  0  1 ]
```

일반적으로 n × n 단위행렬 Iₙ의 원소:

$$
(I_n)_{ij} = \delta_{ij} = 
\begin{cases} 
1 & \text{if } i = j \\
0 & \text{if } i \neq j
\end{cases}
$$

여기서 δᵢⱼ를 **크로네커 델타**(Kronecker delta)라 한다.

---

## 5-d.8 Lean4에서 행렬 표현

### 5-d.8.1 행렬의 타입

Lean4에서 행렬은 **함수**로 표현된다:

```lean
-- m × n 행렬 = Fin m → Fin n → α
-- 즉, (행 인덱스, 열 인덱스) → 원소값

-- 예: 2 × 3 정수 행렬
def Matrix23 := Fin 2 → Fin 3 → Int
```

### 5-d.8.2 구체적인 행렬 정의

```lean
-- 2 × 2 행렬 예제
--     [ 1  2 ]
-- A = [ 3  4 ]

def matA : Fin 2 → Fin 2 → Int := fun i j =>
  match i, j with
  | 0, 0 => 1
  | 0, 1 => 2
  | 1, 0 => 3
  | 1, 1 => 4

-- 원소 접근
#eval matA 0 0  -- 1 (1행 1열)
#eval matA 0 1  -- 2 (1행 2열)
#eval matA 1 0  -- 3 (2행 1열)
#eval matA 1 1  -- 4 (2행 2열)
```

### 5-d.8.3 Mathlib의 Matrix 타입

Mathlib에서는 `Matrix` 타입을 제공한다:

```lean
import Mathlib.Data.Matrix.Basic

-- Matrix m n α = m → n → α
-- 여기서 m, n은 인덱스 타입

-- 2 × 3 실수 행렬
example : Matrix (Fin 2) (Fin 3) ℝ := 
  !![1, 2, 3; 4, 5, 6]

-- !![...] 는 행렬 리터럴 표기법
-- ; 로 행을 구분
```

### 5-d.8.4 특수 행렬 정의

```lean
import Mathlib.Data.Matrix.Basic

open Matrix

-- 영행렬
def zeroMat : Matrix (Fin 2) (Fin 2) Int := 0

-- 단위행렬
def identityMat : Matrix (Fin 2) (Fin 2) Int := 1

-- 확인
#eval zeroMat 0 0      -- 0
#eval identityMat 0 0  -- 1
#eval identityMat 0 1  -- 0
#eval identityMat 1 1  -- 1
```

---

## 5-d.9 행렬의 연산

### 5-d.9.1 행렬의 덧셈

**정의 4**:

> 같은 크기의 두 행렬 A = [aᵢⱼ]와 B = [bᵢⱼ]의 **합** A + B는 각 위치의 원소를 더한 것이다:
> (A + B)ᵢⱼ = aᵢⱼ + bᵢⱼ

**예제**:

```
[ 1  0 ]   [ 0  2 ]   [ 1  2 ]
[ 1  2 ] + [ 3  1 ] = [ 4  3 ]
[ 2  3 ]   [ 1  1 ]   [ 3  4 ]
```

```lean
-- 행렬 덧셈 (직접 구현)
def matAdd (A B : Fin m → Fin n → Int) : Fin m → Fin n → Int :=
  fun i j => A i j + B i j

-- 예제
def A1 : Fin 2 → Fin 2 → Int := fun i j =>
  match i, j with
  | 0, 0 => 1
  | 0, 1 => 2
  | 1, 0 => 3
  | 1, 1 => 4

def B1 : Fin 2 → Fin 2 → Int := fun i j =>
  match i, j with
  | 0, 0 => 5
  | 0, 1 => 6
  | 1, 0 => 7
  | 1, 1 => 8

#eval matAdd A1 B1 0 0  -- 6 (= 1 + 5)
#eval matAdd A1 B1 1 1  -- 12 (= 4 + 8)
```

### 5-d.9.2 행렬의 곱셈

**정의 5** (Rosen 2.6절):

> m × k 행렬 A = [aᵢⱼ]와 k × n 행렬 B = [bᵢⱼ]의 **곱** AB는 m × n 행렬이며:
> (AB)ᵢⱼ = Σₗ₌₁ᵏ aᵢₗ · bₗⱼ

즉, (AB)의 (i, j) 원소는 A의 i행과 B의 j열의 **내적**이다.

**예제**:

```
    [ 1  0  4 ]       [ 2  4 ]
A = [ 2  1  1 ]   B = [ 1  1 ]
    [ 3  1  0 ]       [ 3  0 ]
    [ 0  2  2 ]

AB의 (1,1) 원소 = 1·2 + 0·1 + 4·3 = 2 + 0 + 12 = 14
AB의 (1,2) 원소 = 1·4 + 0·1 + 4·0 = 4 + 0 + 0 = 4
...
```

```lean
-- 행렬 곱셈 (직접 구현)
def matMul (A : Fin m → Fin k → Int) (B : Fin k → Fin n → Int) 
    : Fin m → Fin n → Int :=
  fun i j => 
    Finset.sum (Finset.univ : Finset (Fin k)) fun l => A i l * B l j

-- 간단한 2×2 예제
def M1 : Fin 2 → Fin 2 → Int := fun i j =>
  match i, j with
  | 0, 0 => 1
  | 0, 1 => 2
  | 1, 0 => 3
  | 1, 1 => 4

def M2 : Fin 2 → Fin 2 → Int := fun i j =>
  match i, j with
  | 0, 0 => 5
  | 0, 1 => 6
  | 1, 0 => 7
  | 1, 1 => 8

-- M1 * M2 = [ 1*5+2*7  1*6+2*8 ] = [ 19  22 ]
--           [ 3*5+4*7  3*6+4*8 ]   [ 43  50 ]
```

### 5-d.9.3 행렬 곱셈의 성질

| 성질 | 식 | 성립 여부 |
|------|-----|----------|
| 결합법칙 | (AB)C = A(BC) | ✓ |
| 교환법칙 | AB = BA | ✗ (일반적으로 성립하지 않음) |
| 분배법칙 | A(B + C) = AB + AC | ✓ |
| 단위행렬 | AI = IA = A | ✓ |

```lean
-- 행렬 곱셈은 교환법칙이 성립하지 않는다!
-- 예: AB ≠ BA

-- A = [ 1  1 ]    B = [ 2  1 ]
--     [ 2  1 ]        [ 1  1 ]

-- AB = [ 3  2 ]
--      [ 5  3 ]

-- BA = [ 4  3 ]
--      [ 3  2 ]

-- AB ≠ BA
```

---

## 5-d.10 전치행렬과 대칭행렬

### 5-d.10.1 전치행렬

**정의 6**:

> m × n 행렬 A = [aᵢⱼ]의 **전치행렬**(transpose) Aᵀ는 n × m 행렬이며:
> (Aᵀ)ᵢⱼ = aⱼᵢ

즉, 행과 열을 바꾼 것이다.

**예제**:

```
    [ 1  2  3 ]         [ 1  4 ]
A = [ 4  5  6 ]   Aᵀ = [ 2  5 ]
                        [ 3  6 ]
```

```lean
-- 전치행렬 정의
def transpose (A : Fin m → Fin n → Int) : Fin n → Fin m → Int :=
  fun i j => A j i

-- 예제
def matB : Fin 2 → Fin 3 → Int := fun i j =>
  match i, j with
  | 0, 0 => 1
  | 0, 1 => 2
  | 0, 2 => 3
  | 1, 0 => 4
  | 1, 1 => 5
  | 1, 2 => 6

#eval transpose matB 0 0  -- 1 (원래 0,0)
#eval transpose matB 0 1  -- 4 (원래 1,0)
#eval transpose matB 1 0  -- 2 (원래 0,1)
#eval transpose matB 2 1  -- 6 (원래 1,2)
```

### 5-d.10.2 전치행렬의 성질

| 성질 | 식 |
|------|-----|
| 이중 전치 | (Aᵀ)ᵀ = A |
| 덧셈의 전치 | (A + B)ᵀ = Aᵀ + Bᵀ |
| 곱셈의 전치 | (AB)ᵀ = BᵀAᵀ |

```lean
-- 이중 전치 정리
theorem transpose_transpose (A : Fin m → Fin n → α) :
    transpose (transpose A) = A := by
  funext i j
  rfl
```

### 5-d.10.3 대칭행렬

**정의 7**:

> 정사각 행렬 A가 **대칭행렬**(symmetric matrix)이라는 것은 Aᵀ = A인 것이다.

즉, aᵢⱼ = aⱼᵢ가 모든 i, j에 대해 성립한다.

**예제**:

```
    [ 1  2  3 ]
A = [ 2  5  6 ]   <- 대칭행렬 (aᵢⱼ = aⱼᵢ)
    [ 3  6  9 ]
```

```lean
-- 대칭행렬 정의
def isSymmetric (A : Fin n → Fin n → α) : Prop :=
  ∀ i j, A i j = A j i

-- 예제: 대칭행렬
def symMat : Fin 3 → Fin 3 → Int := fun i j =>
  match i, j with
  | 0, 0 => 1
  | 0, 1 => 2
  | 0, 2 => 3
  | 1, 0 => 2
  | 1, 1 => 5
  | 1, 2 => 6
  | 2, 0 => 3
  | 2, 1 => 6
  | 2, 2 => 9

-- 대칭 증명
example : isSymmetric symMat := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl
```

---

## 5-d.11 0-1 행렬과 부울 곱

### 5-d.11.1 0-1 행렬

**정의 8**:

> **0-1 행렬**(zero-one matrix)은 모든 원소가 0 또는 1인 행렬이다.

0-1 행렬은 **관계**(relation)를 표현하는 데 사용된다.

### 5-d.11.2 0-1 행렬의 연산

**합**(join): A ∨ B

| aᵢⱼ | bᵢⱼ | (A ∨ B)ᵢⱼ |
|-----|-----|----------|
| 0 | 0 | 0 |
| 0 | 1 | 1 |
| 1 | 0 | 1 |
| 1 | 1 | 1 |

**교**(meet): A ∧ B

| aᵢⱼ | bᵢⱼ | (A ∧ B)ᵢⱼ |
|-----|-----|----------|
| 0 | 0 | 0 |
| 0 | 1 | 0 |
| 1 | 0 | 0 |
| 1 | 1 | 1 |

```lean
-- 0-1 행렬의 합 (OR)
def boolJoin (A B : Fin m → Fin n → Bool) : Fin m → Fin n → Bool :=
  fun i j => A i j || B i j

-- 0-1 행렬의 교 (AND)
def boolMeet (A B : Fin m → Fin n → Bool) : Fin m → Fin n → Bool :=
  fun i j => A i j && B i j
```

### 5-d.11.3 부울 곱

**정의 9**:

> m × k 0-1 행렬 A와 k × n 0-1 행렬 B의 **부울 곱**(Boolean product) A ⊙ B는:
> (A ⊙ B)ᵢⱼ = (aᵢ₁ ∧ b₁ⱼ) ∨ (aᵢ₂ ∧ b₂ⱼ) ∨ ... ∨ (aᵢₖ ∧ bₖⱼ)

일반 행렬 곱에서 × → ∧, + → ∨ 로 바꾼 것이다.

**예제**:

```
A = [ 1  0 ]    B = [ 1  1  0 ]
    [ 0  1 ]        [ 0  1  1 ]
    [ 1  0 ]

A ⊙ B의 (1,1) = (1∧1) ∨ (0∧0) = 1 ∨ 0 = 1
A ⊙ B의 (1,2) = (1∧1) ∨ (0∧1) = 1 ∨ 0 = 1
A ⊙ B의 (1,3) = (1∧0) ∨ (0∧1) = 0 ∨ 0 = 0
...

A ⊙ B = [ 1  1  0 ]
        [ 0  1  1 ]
        [ 1  1  0 ]
```

```lean
-- 부울 곱 정의
def boolProd (A : Fin m → Fin k → Bool) (B : Fin k → Fin n → Bool) 
    : Fin m → Fin n → Bool :=
  fun i j => 
    Finset.univ.any fun l => A i l && B l j

-- 예제 행렬
def boolA : Fin 3 → Fin 2 → Bool := fun i j =>
  match i, j with
  | 0, 0 => true
  | 0, 1 => false
  | 1, 0 => false
  | 1, 1 => true
  | 2, 0 => true
  | 2, 1 => false

def boolB : Fin 2 → Fin 3 → Bool := fun i j =>
  match i, j with
  | 0, 0 => true
  | 0, 1 => true
  | 0, 2 => false
  | 1, 0 => false
  | 1, 1 => true
  | 1, 2 => true

#eval boolProd boolA boolB 0 0  -- true
#eval boolProd boolA boolB 0 1  -- true
#eval boolProd boolA boolB 0 2  -- false
```

### 5-d.11.4 부울 곱과 관계의 합성

0-1 행렬이 관계를 나타낼 때, **부울 곱은 관계의 합성**에 해당한다.

- 행렬 M_R이 관계 R을 나타내고
- 행렬 M_S가 관계 S를 나타내면
- M_R ⊙ M_S는 관계 S ∘ R을 나타낸다

---

## 5-d.12 연습문제

### 연습 5-d.1: 전단사 함수와 기수

**문제**: 다음 함수가 단사인지, 전사인지, 전단사인지 판단하라.

```lean
-- (a) f : Nat → Nat, f(n) = n + 1
def f_a : Nat → Nat := fun n => n + 1

-- (b) f : Nat → Nat, f(n) = n / 2
def f_b : Nat → Nat := fun n => n / 2

-- (c) f : Int → Int, f(n) = 2n
def f_c : Int → Int := fun n => 2 * n
```

<details>
<summary>정답 보기</summary>

**(a) f(n) = n + 1**
- **단사**: ✓ (n₁ + 1 = n₂ + 1 → n₁ = n₂)
- **전사**: ✗ (0은 상(image)에 없음)
- **전단사**: ✗

```lean
-- (a) 단사 증명
theorem f_a_injective : Function.Injective f_a := by
  intro a b hab
  omega

-- (a) 전사가 아님
theorem f_a_not_surjective : ¬Function.Surjective f_a := by
  intro h
  -- 0의 원상이 있다고 가정
  obtain ⟨a, ha⟩ := h 0
  -- ha : a + 1 = 0, 자연수에서 불가능
  omega
```

**(b) f(n) = n / 2** (정수 나눗셈)
- **단사**: ✗ (f(0) = f(1) = 0)
- **전사**: ✓ (모든 m에 대해 f(2m) = m)
- **전단사**: ✗

```lean
-- (b) 단사가 아님
theorem f_b_not_injective : ¬Function.Injective f_b := by
  intro h
  have : 0 = 1 := h (by native_decide : f_b 0 = f_b 1)
  omega
```

**(c) f(n) = 2n**
- **단사**: ✓ (2n₁ = 2n₂ → n₁ = n₂)
- **전사**: ✗ (홀수는 상에 없음)
- **전단사**: ✗

```lean
-- (c) 단사 증명
theorem f_c_injective : Function.Injective f_c := by
  intro a b hab
  omega
```

</details>

### 연습 5-d.2: 셀 수 있는 집합

**문제**: 다음 집합이 셀 수 있는지 판단하고, 셀 수 있다면 자연수와의 전단사 함수를 제시하라.

(a) 3의 배수 집합 {0, 3, 6, 9, ...}  
(b) 5보다 큰 소수의 집합  
(c) 무한 이진 문자열의 집합 (예: 0101010..., 1110000..., ...)

<details>
<summary>정답 보기</summary>

**(a) 3의 배수 집합**: 셀 수 있다

전단사 함수: f(n) = 3n

```lean
def triples : Nat → Nat := fun n => 3 * n

-- 단사
theorem triples_injective : Function.Injective triples := by
  intro a b hab
  omega
```

**(b) 5보다 큰 소수의 집합**: 셀 수 있다

소수가 무한히 많으므로 자연수와 일대일 대응 가능:
- 0 → 7 (첫 번째 큰 소수)
- 1 → 11 (두 번째 큰 소수)
- 2 → 13 ...

**(c) 무한 이진 문자열의 집합**: **셀 수 없다**

칸토르 대각선 논증을 적용:
- 모든 무한 이진 문자열을 나열했다고 가정
- 대각선 논증으로 목록에 없는 문자열 구성 가능
- 따라서 셀 수 없다

</details>

### 연습 5-d.3: Finset의 크기

**문제**: 다음 Lean4 코드의 결과를 예측하라.

```lean
import Mathlib.Data.Finset.Card

open Finset

-- (a)
#eval (range 8).card

-- (b)  
#eval ({2, 4, 6, 8, 10} : Finset Nat).card

-- (c)
#eval ((range 5) ∪ (range 3)).card

-- (d)
#eval ((range 5) ∩ {1, 3, 5, 7}).card
```

<details>
<summary>정답 보기</summary>

```lean
-- (a) range 8 = {0, 1, 2, 3, 4, 5, 6, 7}
#eval (range 8).card  -- 8

-- (b) {2, 4, 6, 8, 10}은 5개 원소
#eval ({2, 4, 6, 8, 10} : Finset Nat).card  -- 5

-- (c) range 5 = {0,1,2,3,4}, range 3 = {0,1,2}
-- 합집합 = {0,1,2,3,4}
#eval ((range 5) ∪ (range 3)).card  -- 5

-- (d) range 5 = {0,1,2,3,4} ∩ {1,3,5,7} = {1,3}
#eval ((range 5) ∩ {1, 3, 5, 7}).card  -- 2
```

</details>

### 연습 5-d.4: 행렬 연산

**문제**: 다음 행렬의 덧셈과 곱셈을 계산하라.

```
A = [ 1  2 ]    B = [ 0  1 ]
    [ 3  4 ]        [ 1  0 ]
```

(a) A + B  
(b) AB  
(c) BA  
(d) A²

<details>
<summary>정답 보기</summary>

**(a) A + B**:
```
[ 1+0  2+1 ]   [ 1  3 ]
[ 3+1  4+0 ] = [ 4  4 ]
```

**(b) AB**:
```
(AB)₁₁ = 1·0 + 2·1 = 2
(AB)₁₂ = 1·1 + 2·0 = 1
(AB)₂₁ = 3·0 + 4·1 = 4
(AB)₂₂ = 3·1 + 4·0 = 3

AB = [ 2  1 ]
     [ 4  3 ]
```

**(c) BA**:
```
(BA)₁₁ = 0·1 + 1·3 = 3
(BA)₁₂ = 0·2 + 1·4 = 4
(BA)₂₁ = 1·1 + 0·3 = 1
(BA)₂₂ = 1·2 + 0·4 = 2

BA = [ 3  4 ]
     [ 1  2 ]
```

참고: AB ≠ BA (행렬 곱셈은 교환법칙이 성립하지 않음)

**(d) A²**:
```
(A²)₁₁ = 1·1 + 2·3 = 7
(A²)₁₂ = 1·2 + 2·4 = 10
(A²)₂₁ = 3·1 + 4·3 = 15
(A²)₂₂ = 3·2 + 4·4 = 22

A² = [ 7   10 ]
     [ 15  22 ]
```

</details>

### 연습 5-d.5: 전치행렬과 대칭행렬

**문제**: 다음을 계산하거나 판단하라.

```
    [ 1  2  3 ]
A = [ 4  5  6 ]
```

(a) Aᵀ를 구하라.  
(b) AAᵀ를 구하라.  
(c) AAᵀ가 대칭행렬인지 확인하라.

<details>
<summary>정답 보기</summary>

**(a) Aᵀ**:
```
     [ 1  4 ]
Aᵀ = [ 2  5 ]
     [ 3  6 ]
```

**(b) AAᵀ** (A는 2×3, Aᵀ는 3×2, 결과는 2×2):
```
(AAᵀ)₁₁ = 1·1 + 2·2 + 3·3 = 1 + 4 + 9 = 14
(AAᵀ)₁₂ = 1·4 + 2·5 + 3·6 = 4 + 10 + 18 = 32
(AAᵀ)₂₁ = 4·1 + 5·2 + 6·3 = 4 + 10 + 18 = 32
(AAᵀ)₂₂ = 4·4 + 5·5 + 6·6 = 16 + 25 + 36 = 77

AAᵀ = [ 14  32 ]
      [ 32  77 ]
```

**(c) 대칭 확인**:
(AAᵀ)₁₂ = 32 = (AAᵀ)₂₁ ✓

따라서 AAᵀ는 **대칭행렬**이다.

사실, **모든** 행렬 A에 대해 AAᵀ와 AᵀA는 대칭행렬이다:
(AAᵀ)ᵀ = (Aᵀ)ᵀAᵀ = AAᵀ

</details>

---

## 5-d.13 도전 문제

### 도전 5-d.1: 대각선 논증 구현

**문제**: 칸토르 대각선 논증의 핵심 아이디어를 Lean4로 구현하라.

힌트: 함수 f : Nat → (Nat → Bool)이 전사가 아님을 증명하라.

```lean
-- skeleton
theorem cantor_diag : 
    ∀ f : Nat → (Nat → Bool), ¬Function.Surjective f := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
theorem cantor_diag : 
    ∀ f : Nat → (Nat → Bool), ¬Function.Surjective f := by
  intro f hsurj
  -- 대각선 함수 정의: g(n) = ¬f(n)(n)
  let g : Nat → Bool := fun n => !(f n n)
  -- f가 전사이므로 ∃m, f m = g
  obtain ⟨m, hm⟩ := hsurj g
  -- f m m = g m = !(f m m)
  have : f m m = g m := congrFun hm m
  simp [g] at this
  -- f m m = !(f m m) 는 모순
  -- Bool에서 b = !b 는 불가능
  cases h : f m m
  · simp [h] at this
  · simp [h] at this
```

**설명**:
1. g(n) = ¬f(n)(n)으로 정의 (대각선의 보수)
2. f가 전사라면 어떤 m에서 f(m) = g
3. 그러면 f(m)(m) = g(m) = ¬f(m)(m)
4. 이는 b = ¬b 꼴로 모순

</details>

### 도전 5-d.2: 행렬 곱셈의 결합법칙

**문제**: 2×2 행렬 곱셈이 결합법칙을 만족함을 증명하라.

```lean
-- skeleton
def Mat2 := Fin 2 → Fin 2 → Int

def matMul2 (A B : Mat2) : Mat2 :=
  fun i j => A i 0 * B 0 j + A i 1 * B 1 j

theorem matMul2_assoc (A B C : Mat2) :
    matMul2 (matMul2 A B) C = matMul2 A (matMul2 B C) := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
def Mat2 := Fin 2 → Fin 2 → Int

def matMul2 (A B : Mat2) : Mat2 :=
  fun i j => A i 0 * B 0 j + A i 1 * B 1 j

theorem matMul2_assoc (A B C : Mat2) :
    matMul2 (matMul2 A B) C = matMul2 A (matMul2 B C) := by
  funext i j
  simp only [matMul2]
  -- (AB)C의 (i,j) = Σₖ (AB)ᵢₖ * Cₖⱼ
  --              = Σₖ (Σₗ Aᵢₗ * Bₗₖ) * Cₖⱼ
  --              = Σₖ Σₗ Aᵢₗ * Bₗₖ * Cₖⱼ
  -- A(BC)의 (i,j) = Σₗ Aᵢₗ * (BC)ₗⱼ
  --              = Σₗ Aᵢₗ * (Σₖ Bₗₖ * Cₖⱼ)
  --              = Σₗ Σₖ Aᵢₗ * Bₗₖ * Cₖⱼ
  ring
```

</details>

### 도전 5-d.3: 0-1 행렬과 관계 합성

**문제**: 두 관계의 행렬이 주어졌을 때, 그 합성의 행렬이 부울 곱임을 증명하라.

집합 A = {1, 2, 3}에서의 관계:
- R = {(1,2), (2,3), (3,1)}
- S = {(1,1), (2,2), (3,3)} (항등관계)

```lean
-- skeleton
-- M_R과 M_S의 부울 곱이 S ∘ R의 행렬과 같음을 보이시오

def M_R : Fin 3 → Fin 3 → Bool := fun i j =>
  sorry  -- R의 행렬 표현

def M_S : Fin 3 → Fin 3 → Bool := fun i j =>
  sorry  -- S의 행렬 표현

-- 부울 곱 결과가 S ∘ R의 행렬과 같음
```

<details>
<summary>정답 보기</summary>

```lean
-- R = {(1,2), (2,3), (3,1)}
-- 인덱스를 0-based로: {(0,1), (1,2), (2,0)}
def M_R : Fin 3 → Fin 3 → Bool := fun i j =>
  match i, j with
  | 0, 1 => true
  | 1, 2 => true
  | 2, 0 => true
  | _, _ => false

-- S = {(1,1), (2,2), (3,3)} = 항등관계
-- 인덱스를 0-based로: {(0,0), (1,1), (2,2)}
def M_S : Fin 3 → Fin 3 → Bool := fun i j =>
  if i = j then true else false

-- S ∘ R의 의미: (a,c) ∈ S ∘ R ↔ ∃b, (a,b) ∈ R ∧ (b,c) ∈ S
-- S가 항등관계이므로 (b,c) ∈ S ↔ b = c
-- 따라서 S ∘ R = R (항등관계와의 합성)

-- 부울 곱 계산: M_R ⊙ M_S
def boolProd3 (A B : Fin 3 → Fin 3 → Bool) : Fin 3 → Fin 3 → Bool :=
  fun i j => (A i 0 && B 0 j) || (A i 1 && B 1 j) || (A i 2 && B 2 j)

-- M_R ⊙ M_S = M_R (항등행렬과의 부울 곱)
example : boolProd3 M_R M_S = M_R := by
  funext i j
  fin_cases i <;> fin_cases j <;> native_decide
```

</details>

---

## 5-d.14 전술 요약

### 집합의 크기 관련

| 전술/정리 | 용도 | 예시 |
|---------|------|------|
| `Finset.card` | 유한 집합의 크기 | `(range 5).card` |
| `Fintype.card` | 유한 타입의 크기 | `Fintype.card (Fin n)` |
| `card_empty` | ∅의 크기는 0 | `(∅ : Finset Nat).card = 0` |
| `card_union_of_disjoint` | 서로소 합집합의 크기 | \|A ∪ B\| = \|A\| + \|B\| |

### 함수 관련

| 정의/전술 | 용도 |
|---------|------|
| `Function.Injective` | 단사 함수 |
| `Function.Surjective` | 전사 함수 |
| `Function.Bijective` | 전단사 함수 |
| `omega` | 선형 산술 자동 증명 |

### 행렬 관련

| 개념 | Lean4 표현 |
|------|-----------|
| m × n 행렬 | `Fin m → Fin n → α` |
| 행렬 덧셈 | `fun i j => A i j + B i j` |
| 행렬 곱셈 | `fun i j => ∑ k, A i k * B k j` |
| 전치행렬 | `fun i j => A j i` |

### 핵심 개념 요약

| 개념 | 정의 |
|------|------|
| 같은 기수 | 전단사 함수 존재 |
| 셀 수 있음 | 유한이거나 ℕ과 전단사 |
| 셀 수 없음 | ℕ과 전단사 불가능 |
| 대각선 논증 | 셀 수 없음의 증명 방법 |
| 대칭행렬 | Aᵀ = A |
| 부울 곱 | ∨와 ∧를 사용한 행렬 곱 |

---

## 다음 편 예고

**제6편**에서는 **그래프 이론**의 기초를 다룬다:

- 그래프의 정의와 표현
- 경로와 회로
- 오일러 경로와 해밀턴 경로
- 최단 경로 알고리즘

을 학습한다.

---

**(끝)**
