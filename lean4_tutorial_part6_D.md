# Lean4 완전 정복 가이드 — 제6-D편

## **Big-Omega**(Ω), **Big-Theta**(Θ), 그리고 **알고리즘의 복잡도**(Complexity) 완전 정복

> **교재**: Kenneth H. Rosen, "Discrete Mathematics and Its Applications" 8판  
> **범위**: 3.2절 후반부(Big-Omega, Big-Theta), 3.3절 알고리즘의 복잡도  
> **선수 학습**: 제6-C편(Big-O 표기법, 정리/보조정리, →/↔ 차이)

---

## 6D.0 이 장의 목표

이 장에서 다루는 핵심 내용은 다음과 같다:

1. **Big-Omega**(Ω): 함수의 증가에 대한 **하한**(lower bound)
2. **Big-Theta**(Θ): 함수의 증가에 대한 **상한과 하한을 동시에** 나타내는 표기
3. **동차**(same order): 두 함수가 Θ 관계일 때
4. **시간복잡도**(time complexity)란 무엇인지
5. **최악의 경우**(worst case) 분석
6. 교재의 연습문제들을 Lean4로 변환

---

## 6D.1 **Big-Omega**(Ω) 표기법

### 6D.1.1 Big-O는 상한, Big-Omega는 하한

제6-C편에서 배운 Big-O는 함수의 증가에 대한 **상한**(upper bound)을 제공한다. 즉, "f(x)는 **아무리 크게 잡아도** g(x)의 상수배 이하이다"라는 것이다.

하지만 상한만으로는 부족할 때가 있다. 예를 들어 "n²은 O(n¹⁰⁰)이다"라고 해도 틀린 말은 아니지만, n²의 실제 증가 속도를 정확히 반영하지 못한다.

**Big-Omega**(Ω)는 반대 방향이다: 함수의 증가에 대한 **하한**을 제공한다.

### 6D.1.2 Big-Omega의 정식 정의 (교재 정의 2, p.255)

> **정의**: f와 g가 정수 집합(또는 실수 집합)에서 실수로의 함수라 하자. x > k일 때 항상 |f(x)| ≥ C|g(x)|를 만족하는 **양의 상수** C와 k가 존재하면, f(x)는 Ω(g(x))라고 한다.

기호로:

```
f(x) ∈ Ω(g(x))  ⟺  ∃ C > 0, ∃ k, ∀ x > k, f(x) ≥ C · g(x)
```

Big-O와 비교하면:
- **Big-O**: f(x) ≤ C · g(x) (위에서 누른다 = **상한**)
- **Big-Omega**: f(x) ≥ C · g(x) (아래에서 받친다 = **하한**)

### 6D.1.3 Lean4에서 Big-Omega 정의

```lean
-- Big-Omega 정의 (자연수 버전)
def IsBigOmega (f g : Nat → Nat) : Prop :=
  ∃ C k, C > 0 ∧ ∀ x, x > k → f x ≥ C * g x
```

Big-O와 거의 같지만, 부등호 방향이 `≤`에서 `≥`로 바뀌었고, C > 0 조건이 추가되었다.

### 6D.1.4 교재 예제 11: 8x³ + 5x² + 7은 Ω(x³)

**교재 풀이** (p.255): 모든 양의 실수 x에 대해 f(x) = 8x³ + 5x² + 7 ≥ 8x³이므로 C = 8, k = 0이 증인이다.

또한 g(x) = x³이므로 이는 O(8x³ + 5x² + 7)임도 동등하다 (부등식 방향을 뒤집으면).

```lean
theorem ex11_big_omega :
    IsBigOmega (fun x => 8 * x ^ 3 + 5 * x ^ 2 + 7) (fun x => x ^ 3) := by
  use 8, 0
  constructor
  · omega
  · intro x hx
    nlinarith [sq_nonneg x]
```

### 6D.1.5 Big-O와 Big-Omega의 관계

중요한 사실: **f(x)가 Ω(g(x))인 것은 g(x)가 O(f(x))인 것의 필요충분조건**이다.

즉, `f(x) ∈ Ω(g(x))` ↔ `g(x) ∈ O(f(x))`.

직관: f가 g보다 "크거나 같은 속도로 자란다" ↔ g가 f보다 "작거나 같은 속도로 자란다".

---

## 6D.2 **Big-Theta**(Θ) 표기법

### 6D.2.1 Big-Theta의 필요성

Big-O만으로는 "이 알고리즘은 **정확히** n² 정도의 시간이 걸린다"라고 말하기 어렵다. n²은 O(n²)이지만 O(n³)이기도 하고, O(n¹⁰⁰)이기도 하다.

**Big-Theta**(Θ)는 **상한과 하한을 동시에** 나타내서, 함수의 정확한 증가 속도를 표현한다.

### 6D.2.2 Big-Theta의 정식 정의 (교재 정의 3, p.255)

> **정의**: f(x)가 O(g(x))이고 동시에 f(x)가 Ω(g(x))이면, f(x)는 Θ(g(x))라 한다. 이때 "f는 g(x)의 **차수**(order)를 갖는다"고 하며, f(x)와 g(x)는 **동차**(same order)라고 한다.

동등한 표현:

```
f(x) ∈ Θ(g(x))  ⟺  ∃ C₁ C₂ k, ∀ x > k, C₁·g(x) ≤ f(x) ≤ C₂·g(x)
```

즉, f(x)가 g(x)의 **C₁배와 C₂배 사이에 끼여 있다**는 뜻이다.

### 6D.2.3 Lean4에서 Big-Theta 정의

```lean
-- Big-Theta 정의
def IsBigTheta (f g : Nat → Nat) : Prop :=
  IsBigO f g ∧ IsBigOmega f g
```

Big-Theta = Big-O + Big-Omega이다. 이것은 **쌍조건문**(↔)과 비슷한 구조이다:
- Big-O만 있으면 → (한쪽 방향: 상한만)
- Big-Theta가 있으면 ↔ (양쪽 방향: 상한 + 하한)

### 6D.2.4 교재 예제 12: 첫 n개의 합은 Θ(n²)

**교재 풀이** (p.256):

f(n) = 1 + 2 + ... + n = n(n+1)/2

- **O(n²)**: f(n) ≤ n² (예제 5에서 이미 보임)
- **Ω(n²)**: 합의 절반 이상의 항만 더해도 하한을 얻는다
  - ⌈n/2⌉ + (⌈n/2⌉+1) + ... + n ≥ ⌈n/2⌉ · (n - ⌈n/2⌉ + 1) ≥ (n/2)(n/2) = n²/4

따라서 f(n)은 Θ(n²)이다.

### 6D.2.5 교재 예제 13: 3x² + 8x log x는 Θ(x²)

**교재 풀이** (p.256):

- **O(x²)**: 0 ≤ 8x log x ≤ 8x²이므로 3x² + 8x log x ≤ 11x²
- **Ω(x²)**: 3x² + 8x log x ≥ 3x² (8x log x ≥ 0이므로)

증인: C₁ = 3, C₂ = 11, k = 1이다.

---

## 6D.3 세 표기법 비교

| 표기법 | 의미 | 부등호 | 직관 |
|--------|------|--------|------|
| **O**(g) | f는 g의 상수배 **이하** | f ≤ C·g | "f는 g보다 **빨리 자라지 않는다**" |
| **Ω**(g) | f는 g의 상수배 **이상** | f ≥ C·g | "f는 g보다 **느리게 자라지 않는다**" |
| **Θ**(g) | f는 g와 **같은 속도** | C₁·g ≤ f ≤ C₂·g | "f는 g와 **같은 차수**이다" |

**핵심 관계**:

```
f ∈ Θ(g)  ⟺  f ∈ O(g) ∧ f ∈ Ω(g)
```

---

## 6D.4 연습 세트 1: Ω, Θ 기초

### 연습 6D.1: Big-Omega 증명 (괄호 채우기)

```lean
-- 5x² + 3은 Ω(x²)
-- 증인: C = ▢, k = ▢
theorem ex_omega1 :
    IsBigOmega (fun x => 5 * x ^ 2 + 3) (fun x => x ^ 2) := by
  use ▢, ▢
  constructor
  · omega
  · intro x hx
    nlinarith [sq_nonneg x]
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem ex_omega1 :
    IsBigOmega (fun x => 5 * x ^ 2 + 3) (fun x => x ^ 2) := by
  use 5, 0
  constructor
  · omega
  · intro x hx
    nlinarith [sq_nonneg x]
```

5x² + 3 ≥ 5x²이므로 C = 5로 충분하다.

</details>

### 연습 6D.2: Big-Theta 증명 (sorry)

```lean
-- 4x² + x는 Θ(x²)
theorem ex_theta1 :
    IsBigTheta (fun x => 4 * x ^ 2 + x) (fun x => x ^ 2) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem ex_theta1 :
    IsBigTheta (fun x => 4 * x ^ 2 + x) (fun x => x ^ 2) := by
  constructor
  · -- O(x²) 파트: 4x² + x ≤ 5x² (x > 1일 때)
    use 5, 1
    intro x hx
    nlinarith [sq_nonneg x]
  · -- Ω(x²) 파트: 4x² + x ≥ 4x²
    use 4, 0
    constructor
    · omega
    · intro x hx
      nlinarith [sq_nonneg x]
```

</details>

### 연습 6D.3: Θ 분해 (sorry)

**문제**: Big-Theta에서 Big-O 부분만 추출하시오.

```lean
-- h : IsBigTheta f g에서 IsBigO f g 추출
example (f g : Nat → Nat) (h : IsBigTheta f g) : IsBigO f g := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
example (f g : Nat → Nat) (h : IsBigTheta f g) : IsBigO f g := by
  exact h.1
```

`IsBigTheta`가 `∧`(and)으로 정의되어 있으므로, `.1`으로 첫 번째 부분(Big-O)을 추출한다.

</details>

### 연습 6D.4: 교재 연습문제 28~29 유형 (sorry)

**문제**: 다음 함수가 Ω(x²)인지, Θ(x²)인지 판정하시오.

```lean
-- (a) 17x + 11은 Ω(x²)인가? → 아니다!
-- (17x + 11은 O(x)이고 x는 O(x²)이지만, x²은 O(17x+11)이 아니다)
theorem ex28a : ¬ IsBigOmega (fun x => 17 * x + 11) (fun x => x ^ 2) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem ex28a : ¬ IsBigOmega (fun x => 17 * x + 11) (fun x => x ^ 2) := by
  intro ⟨C, k, hC, h⟩
  -- x = 17*C + k + 11 을 대입하면 모순
  have hx := h (17 * C + k + 11) (by omega)
  nlinarith [sq_nonneg (17 * C + k + 11)]
```

17x + 11 ≥ C·x²이면 x가 충분히 크면 성립할 수 없다 (선형 < 이차).

</details>

### 연습 6D.5: 교재 연습문제 30 유형 — 동차 판정 (sorry)

**문제**: 3x + 7과 x가 같은 차수(Θ)인지 보이시오.

```lean
-- 3x + 7과 x는 동차
theorem same_order_3x7 :
    IsBigTheta (fun x => 3 * x + 7) (fun x => x) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem same_order_3x7 :
    IsBigTheta (fun x => 3 * x + 7) (fun x => x) := by
  constructor
  · -- O(x): 3x + 7 ≤ 10x (x > 0일 때)
    use 10, 0
    intro x hx
    omega
  · -- Ω(x): 3x + 7 ≥ 1·x
    use 1, 0
    constructor
    · omega
    · intro x hx
      omega
```

</details>

---

## 6D.5 **알고리즘의 시간복잡도**(Time Complexity)

### 6D.5.1 시간복잡도란?

**시간복잡도**(time complexity)란 알고리즘이 입력 크기 n에 대해 수행하는 **기본 연산의 횟수**를 함수로 나타낸 것이다.

사용하는 연산은 정수의 비교, 덧셈, 곱셈, 나눗셈 등이다.

**왜 실제 시간이 아니라 연산 횟수를 세는가?**
- 실제 실행시간은 컴퓨터마다 다르다
- 연산의 실행시간은 컴퓨터마다 기본 비트 연산 수준에서 달라진다
- 하지만 **연산 횟수**는 알고리즘 자체의 속성이므로, 하드웨어에 무관하다

### 6D.5.2 최악의 경우 분석

알고리즘의 시간복잡도를 말할 때, 보통 **최악의 경우**(worst case)를 기준으로 한다.

**최악의 경우**: 크기 n인 모든 가능한 입력 중에서, 알고리즘이 **가장 많은 연산**을 수행하는 경우.

왜 최악의 경우를 분석하는가?
- **보장을 제공한다**: "이 알고리즘은 **어떤 입력이 오더라도** 최대 이만큼의 시간이 걸린다"
- **안전하다**: 최악의 경우를 알면, 그보다 더 나쁘진 않다
- **실용적이다**: 특히 실시간 시스템에서는 최악의 경우가 중요하다

---

## 6D.6 교재 3.3절: 구체적 알고리즘 분석

### 6D.6.1 교재 예제 1: 최댓값 찾기

알고리즘: 리스트의 최댓값을 찾는 알고리즘 (제6-A편에서 구현)

```
procedure max(a₁, a₂, ..., aₙ : integers)
max := a₁
for i := 2 to n
    if aᵢ > max then max := aᵢ
return max
```

**비교 연산 횟수 분석**:
- for 루프가 i = 2부터 n까지 돌므로, **정확히 n - 1번**의 비교가 이루어진다
- 이것은 **입력이 무엇이든** (최악이든 최선이든) 동일하다
- 따라서 시간복잡도는 **Θ(n)** (선형)

```lean
-- 최댓값 알고리즘의 비교 횟수
-- n개의 원소를 가진 리스트에서 최댓값을 찾으려면 n-1번 비교
def comparisons_max (n : Nat) : Nat := n - 1

-- n-1은 Θ(n)
theorem max_complexity : IsBigTheta comparisons_max (fun n => n) := by
  constructor
  · -- O(n): n - 1 ≤ 1 * n
    use 1, 0
    intro x hx
    unfold comparisons_max
    omega
  · -- Ω(n): n - 1 ≥ 1 * n / 2 (n > 2일 때)
    -- 더 정확히: n - 1 ≥ (1/2) * n, 즉 2(n-1) ≥ n
    use 1, 1
    constructor
    · omega
    · intro x hx
      unfold comparisons_max
      omega
```

### 6D.6.2 교재 예제 2: 선형 탐색

알고리즘: 리스트에서 특정 원소 x를 찾는 선형 탐색

**비교 연산 횟수 분석**:
- **최선의 경우**: x가 첫 번째 원소일 때, **1번** 비교
- **최악의 경우**: x가 리스트에 없거나 마지막에 있을 때, **n번** 비교
- 최악의 경우 시간복잡도: **Θ(n)**

### 6D.6.3 교재 예제 3: 이진 탐색

알고리즘: 정렬된 리스트에서 특정 원소 x를 찾는 이진 탐색

**비교 연산 횟수 분석**:
- 각 단계에서 리스트의 크기가 **절반**으로 줄어든다
- n개의 원소가 있을 때, 최대 **⌊log₂ n⌋ + 1번** 비교
- 최악의 경우 시간복잡도: **Θ(log n)**

```lean
-- 이진 탐색의 최악의 경우 비교 횟수 (근사)
-- 정확히는 ⌊log₂ n⌋ + 1이지만, 이는 O(log n)
-- Lean4에서 Nat.log를 사용
def comparisons_binary_search (n : Nat) : Nat := Nat.log 2 n + 1
```

### 6D.6.4 교재 예제 4: 버블 정렬

알고리즘: 인접한 원소를 비교하여 정렬하는 버블 정렬

**비교 연산 횟수 분석**:
- 첫 번째 패스: n-1번 비교
- 두 번째 패스: n-2번 비교
- ...
- 마지막 패스: 1번 비교
- 총 비교 횟수: (n-1) + (n-2) + ... + 1 = **n(n-1)/2**
- 시간복잡도: **Θ(n²)**

```lean
-- 버블 정렬의 비교 횟수
def comparisons_bubble (n : Nat) : Nat := n * (n - 1) / 2

-- n(n-1)/2는 Θ(n²) — 이를 증명하는 것은 복잡하므로 O(n²)만 증명
theorem bubble_O_n2 : IsBigO comparisons_bubble (fun n => n ^ 2) := by
  use 1, 0
  intro x hx
  unfold comparisons_bubble
  -- x*(x-1)/2 ≤ x²
  omega
```

### 6D.6.5 교재 예제 5: 삽입 정렬

**비교 연산 횟수 분석 (최악의 경우)**:
- 두 번째 원소 삽입: 최대 1번 비교
- 세 번째 원소 삽입: 최대 2번 비교
- ...
- n번째 원소 삽입: 최대 n-1번 비교
- 총: 1 + 2 + ... + (n-1) = **n(n-1)/2**
- 시간복잡도: **Θ(n²)** (최악의 경우)

---

## 6D.7 복잡도 클래스 정리

| 복잡도 | 클래스 이름 | 예시 알고리즘 |
|--------|-----------|------------|
| Θ(1) | **상수** 시간 | 배열 인덱스 접근 |
| Θ(log n) | **로그** 시간 | **이진 탐색** |
| Θ(n) | **선형** 시간 | **선형 탐색**, 최댓값 찾기 |
| Θ(n log n) | **선형로그** 시간 | **병합 정렬** |
| Θ(n²) | **이차** 시간 | **버블 정렬**, **삽입 정렬** |
| Θ(n³) | **삼차** 시간 | 행렬 곱셈 (단순) |
| Θ(2ⁿ) | **지수** 시간 | 부분집합 나열 |
| Θ(n!) | **계승** 시간 | 순열 나열 |

**실용적 의미**: n이 100만(10⁶)일 때:

| 복잡도 | 연산 횟수 (대략) | 소요 시간 (10⁹/초 기준) |
|--------|---------------|---------------------|
| Θ(log n) | 20 | 0.00000002초 |
| Θ(n) | 10⁶ | 0.001초 |
| Θ(n log n) | 2 × 10⁷ | 0.02초 |
| Θ(n²) | 10¹² | 약 17분 |
| Θ(n³) | 10¹⁸ | 약 30년 |
| Θ(2ⁿ) | 10³⁰⁰⁰⁰⁰ | 우주보다 오래 |

---

## 6D.8 연습 세트 2: 시간복잡도

### 연습 6D.6: 알고리즘 복잡도 판별 (괄호 채우기)

**문제**: 각 알고리즘의 시간복잡도를 빈칸에 채우시오.

```
(a) 최댓값 찾기 (n개 원소): Θ(▢)
(b) 선형 탐색 (최악): Θ(▢)
(c) 이진 탐색 (최악): Θ(▢)
(d) 버블 정렬: Θ(▢)
```

<details>
<summary>💡 답 보기</summary>

```
(a) Θ(n)
(b) Θ(n)
(c) Θ(log n)
(d) Θ(n²)
```

</details>

### 연습 6D.7: 비교 횟수 계산 (sorry)

**문제**: n = 8인 리스트에서 각 알고리즘의 최악의 경우 비교 횟수를 계산하시오.

```lean
-- 선형 탐색: n = 8
#eval (8 : Nat)  -- 답: ▢

-- 이진 탐색: ⌊log₂ 8⌋ + 1 = ▢
#eval Nat.log 2 8 + 1

-- 버블 정렬: 8 * 7 / 2 = ▢
#eval 8 * 7 / 2
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval (8 : Nat)            -- 선형 탐색: 8
#eval Nat.log 2 8 + 1     -- 이진 탐색: 4 (3 + 1)
#eval 8 * 7 / 2           -- 버블 정렬: 28
```

</details>

### 연습 6D.8: O(n²) 증명 (sorry)

**문제**: 다음 함수가 O(n²)임을 증명하시오.

```lean
-- f(n) = 3n + 5는 O(n²)인가?
theorem ex_3n5_O_n2 : IsBigO (fun n => 3 * n + 5) (fun n => n ^ 2) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem ex_3n5_O_n2 : IsBigO (fun n => 3 * n + 5) (fun n => n ^ 2) := by
  use 8, 1
  intro x hx
  nlinarith [sq_nonneg x]
```

x > 1이면 3x ≤ 3x², 5 ≤ 5x²이므로 3x + 5 ≤ 8x².

</details>

### 연습 6D.9: Θ(n²) 증명 (sorry)

**문제**: n² + n은 Θ(n²)임을 증명하시오.

```lean
theorem ex_n2_n_theta :
    IsBigTheta (fun n => n ^ 2 + n) (fun n => n ^ 2) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem ex_n2_n_theta :
    IsBigTheta (fun n => n ^ 2 + n) (fun n => n ^ 2) := by
  constructor
  · -- O(n²): n² + n ≤ 2n²
    use 2, 1
    intro x hx
    nlinarith [sq_nonneg x]
  · -- Ω(n²): n² + n ≥ 1 · n²
    use 1, 0
    constructor
    · omega
    · intro x hx
      nlinarith
```

</details>

### 연습 6D.10: 교재 연습문제 유형 — 알고리즘 비교 (서술형)

**문제**: 크기 n인 문제를 푸는 두 알고리즘이 있다. 알고리즘 A는 100n² + 17n + 4개의 연산을, 알고리즘 B는 n³개의 연산을 사용한다. n이 커짐에 따라 어느 알고리즘이 더 효율적인지 Lean4로 보이시오.

```lean
-- A의 연산 횟수
def ops_A (n : Nat) : Nat := 100 * n ^ 2 + 17 * n + 4
-- B의 연산 횟수
def ops_B (n : Nat) : Nat := n ^ 3

-- A는 O(n²), B는 O(n³)
-- n이 충분히 크면 A가 더 효율적

-- (1) A는 O(n²)
theorem A_is_O_n2 : IsBigO ops_A (fun n => n ^ 2) := by
  sorry

-- (2) B는 O(n³)이지만 O(n²)가 아님
theorem B_is_O_n3 : IsBigO ops_B (fun n => n ^ 3) := by
  sorry

theorem B_not_O_n2 : ¬ IsBigO ops_B (fun n => n ^ 2) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem A_is_O_n2 : IsBigO ops_A (fun n => n ^ 2) := by
  use 121, 1
  intro x hx
  unfold ops_A
  nlinarith [sq_nonneg x]

theorem B_is_O_n3 : IsBigO ops_B (fun n => n ^ 3) := by
  use 1, 0
  intro x hx
  unfold ops_B
  omega

theorem B_not_O_n2 : ¬ IsBigO ops_B (fun n => n ^ 2) := by
  intro ⟨C, k, h⟩
  have hx := h (C + k + 1) (by omega)
  unfold ops_B at hx
  nlinarith [sq_nonneg (C + k + 1)]
```

A는 Θ(n²), B는 Θ(n³)이다. n² ≪ n³이므로, n이 충분히 크면 A가 더 효율적이다.

</details>

---

## 6D.9 도전 문제

### 도전 6D.1: Big-O ↔ Big-Omega 관계 증명

**문제**: f가 O(g)이면 g가 Ω(f)임을 보이시오 (간소화 버전).

```lean
-- 힌트: IsBigO f g의 증인을 IsBigOmega g f의 증인으로 변환
-- (이 증명은 Nat에서 약간 까다로울 수 있다)
theorem big_o_imp_big_omega_simple :
    IsBigO (fun x => 2 * x) (fun x => x) →
    IsBigOmega (fun x => x) (fun x => 2 * x) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem big_o_imp_big_omega_simple :
    IsBigO (fun x => 2 * x) (fun x => x) →
    IsBigOmega (fun x => x) (fun x => 2 * x) := by
  intro ⟨C, k, h⟩
  -- 2x ≤ C * x이므로, x ≥ (1/C) * 2x ≥ 1 * 2x / C
  -- 하지만 Nat에서는 나눗셈이 까다로우므로 직접 증인 제시
  use 1, k
  constructor
  · omega
  · intro x hx
    omega
```

</details>

### 도전 6D.2: Θ의 대칭성

**문제**: f가 Θ(g)이면 g도 Θ(f)인가? 이 성질을 **대칭성**(symmetry)이라 한다. 특수한 경우를 증명하시오.

```lean
-- 힌트: Θ = O ∧ Ω이고, O와 Ω는 서로 역관계
-- 간소화 버전
theorem theta_symm_simple :
    IsBigTheta (fun x => 3 * x) (fun x => x) →
    IsBigTheta (fun x => x) (fun x => 3 * x) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem theta_symm_simple :
    IsBigTheta (fun x => 3 * x) (fun x => x) →
    IsBigTheta (fun x => x) (fun x => 3 * x) := by
  intro ⟨ho, homega⟩
  constructor
  · -- O(3x): x ≤ 1 * 3x
    use 1, 0
    intro x hx
    omega
  · -- Ω(3x): x ≥ ... 
    -- 실은 3x ≤ C * x이므로 x ≥ (1/C) * 3x
    use 1, 0
    constructor
    · omega
    · intro x hx
      omega
```

</details>

---

## 6D.10 전술 요약

### 이 장의 새로운 개념

| 개념 | 정의 |
|------|------|
| `IsBigOmega f g` | ∃ C > 0, ∃ k, ∀ x > k, f x ≥ C * g x |
| `IsBigTheta f g` | IsBigO f g ∧ IsBigOmega f g |
| **시간복잡도** | 입력 크기 n에 대한 기본 연산 횟수 |
| **최악의 경우** | 모든 입력 중 가장 많은 연산이 필요한 경우 |

### Lean4 전술 복습

| 전술 | 용도 | 이 장에서의 사용 |
|------|------|-------------|
| `constructor` | ∧ 또는 ↔ 분리 | Θ = O ∧ Ω 증명 |
| `use` | ∃ 증인 제시 | C, k 선택 |
| `obtain` | ∃ 분해 | ⟨C, k, h⟩ 추출 |
| `nlinarith` | 비선형 산술 | 부등식 증명 |
| `omega` | 선형 산술 | 간단한 부등식 |
| `.1` / `.2` | ∧의 양쪽 추출 | Θ에서 O 또는 Ω 추출 |

---

## 6D.11 핵심 정리 요약

1. **Big-O**(O) = 상한, **Big-Omega**(Ω) = 하한, **Big-Theta**(Θ) = 상한 + 하한 = 동차

2. **Θ(g)는 가장 정확한 표현**이다. O(g)만으로는 지나치게 느슨할 수 있다.

3. **시간복잡도**는 입력 크기에 따른 연산 횟수이며, 보통 **최악의 경우**를 분석한다.

4. 주요 알고리즘의 복잡도:
   - 최댓값 찾기: Θ(n)
   - 선형 탐색: Θ(n) (최악)
   - 이진 탐색: Θ(log n) (최악)
   - 버블/삽입 정렬: Θ(n²) (최악)

5. **알고리즘 비교**: Θ 분석을 통해 n이 충분히 클 때 어떤 알고리즘이 더 효율적인지 판단할 수 있다.

---

## 다음 편 예고

다음 편에서는:
- **수학적 귀납법**(Mathematical Induction)과 Lean4의 `induction` 전술
- **강한 귀납법**(Strong Induction)
- **재귀적 정의**(Recursive Definitions)와 그 정확성 증명

을 다룬다.

---

**(끝)**
