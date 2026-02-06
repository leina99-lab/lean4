# Lean4 완전 정복 가이드 — 제6-E편

## **알고리즘 복잡도 연습**(Algorithm Complexity Exercises) — 연산 횟수의 Big-O 추정

> **교재**: Kenneth H. Rosen, "Discrete Mathematics and Its Applications" 8판  
> **범위**: 3.3절 연습문제 1~12  
> **선수 학습**: 제6-C편(Big-O 표기법), 제6-D편(Ω, Θ, 시간복잡도)  
> **참고**: 『Mathematics in Lean』 Chapter 2 (Basics: 부등식 증명)

---

## 6E.0 이 장의 목표

이 장에서는 3.3절 연습문제를 Lean4 코드로 직접 풀어본다. 핵심 목표는 다음과 같다:

1. **루프**(loop) 구조를 보고 **연산 횟수**를 정확히 세는 방법
2. 세어진 연산 횟수가 어떤 함수의 **Big-O**인지 증명하는 방법
3. **중첩 루프**(nested loops)에서 총 연산 횟수를 계산하는 방법
4. 이 모든 것을 Lean4의 `Nat` 타입과 부등식 전술로 형식화하는 방법

---

## 6E.1 기초 복습: 루프와 연산 횟수 세기

### 6E.1.1 단일 루프의 연산 횟수

알고리즘에서 **기본 연산**(basic operation)이란, 덧셈, 곱셈, 비교 등 한 번에 수행 가능한 연산을 말한다. 알고리즘의 **시간복잡도**(time complexity)는 입력 크기 `n`에 대해 이 기본 연산이 몇 번 수행되는지를 함수로 나타낸 것이다.

가장 간단한 예부터 살펴보자.

```
t := 0
for i := 1 to n
    t := t + 1
```

이 알고리즘에서 **덧셈**(`t + 1`)은 정확히 **n번** 실행된다. 루프가 `i = 1`부터 `i = n`까지 돌기 때문이다. 따라서 이 알고리즘의 연산 횟수는 **f(n) = n**이다.

Lean4에서 이것을 어떻게 표현할까? 먼저 "연산 횟수를 세는 함수"를 직접 정의한다.

```lean
-- 단일 루프: i가 1부터 n까지 → 연산 n번
def ops_single_loop (n : Nat) : Nat := n
```

너무 간단해 보이지만, 이것이 출발점이다. 핵심은 **루프의 반복 횟수 = 연산 횟수**라는 점이다.

### 6E.1.2 이중 루프의 연산 횟수

이제 루프가 두 겹인 경우를 보자.

```
t := 0
for i := 1 to n
    for j := 1 to n
        t := t + 1
```

바깥 루프는 `i = 1`부터 `n`까지, 안쪽 루프는 `j = 1`부터 `n`까지 돈다. 바깥 루프의 각 반복마다 안쪽 루프가 `n`번 실행되므로, 총 연산 횟수는:

$$n \times n = n^2$$

이것을 Lean4로 표현하면 다음과 같다.

```lean
-- 이중 루프: n × n = n² 번 연산
def ops_double_loop (n : Nat) : Nat := n ^ 2
```

### 6E.1.3 바깥 루프와 안쪽 루프의 범위가 다른 경우

교재의 연습문제 1번은 다음과 같은 알고리즘이다:

```
t := 0
for i := 1 to 3
    for j := 1 to 4
        t := t + ij
```

여기서 기본 연산은 **덧셈과 곱셈**이다. 연산의 종류를 구분하지 않고 "한 번의 루프 실행 = 한 번의 연산"으로 세면, 바깥 루프는 3번, 안쪽 루프는 4번 → 총 `3 × 4 = 12`번이다.

하지만 잠깐! 이 알고리즘에서 `n`은 어디 있는가? 바깥 루프가 `1 to 3`, 안쪽 루프가 `1 to 4`로 **상수**이다. 따라서 입력 크기에 관계없이 연산 횟수가 일정하다. 이런 경우를 **상수 시간**(constant time)이라 하고, **O(1)**이라 표기한다.

> **핵심 포인트**: 루프의 범위가 `n`에 의존하지 않으면, 그 알고리즘은 **O(1)**이다.

그러나 교재 문제의 의도는 "이런 구조를 가진 일반적인 알고리즘의 Big-O를 추정하라"는 것이다. 만약 `for i := 1 to 3`이 `for i := 1 to n`으로, `for j := 1 to 4`가 `for j := 1 to m`으로 바뀐다면 연산 횟수는 `n × m`이 된다.

---

## 6E.2 교재 연습문제 1번: Big-O 추정 (상수 범위 루프)

### 문제 원문

> 아래 알고리즘의 연산 횟수를 Big-O로 추정하라. (연산은 덧셈이나 곱셈이다.)
>
> ```
> t := 0
> for i := 1 to 3
>     for j := 1 to 4
>         t := t + ij
> ```

### 풀이: 연산 횟수 세기

이 알고리즘을 단계별로 분석해보자.

**1단계**: 바깥 루프 `for i := 1 to 3`은 **3번** 반복한다.

**2단계**: 안쪽 루프 `for j := 1 to 4`는 **4번** 반복한다.

**3단계**: 각 반복에서 `i * j` (곱셈 1번)와 `t + ij` (덧셈 1번)이 실행된다. 이것을 "연산 2번"으로 세거나, "루프 본문 실행 1번"으로 셀 수 있다. 보통 Big-O 분석에서는 **주된 연산**(dominant operation)만 세므로, 곱셈 또는 덧셈 하나만 기본 연산으로 삼는다.

**4단계**: 총 연산 횟수 = 3 × 4 = **12번** (곱셈이나 덧셈 각각 12번).

**5단계**: 12는 상수이므로, 이 알고리즘은 **O(1)**이다.

### Lean4 풀이

```lean
-- 연습문제 1: 상수 범위 루프의 연산 횟수
-- 연산 횟수가 상수(12)이므로 O(1)

def ops_ex1 : Nat := 3 * 4  -- = 12

-- "12는 O(1)이다"를 증명하자.
-- 여기서 "O(1)"이란: ∃ C k, ∀ n > k, 12 ≤ C * 1
-- 상수 함수이므로 자명하다.

-- 우선 Big-O 정의를 다시 가져오자 (6-C편에서 정의한 것)
def IsBigO (f g : Nat → Nat) : Prop :=
  ∃ C : Nat, ∃ k : Nat, ∀ n : Nat, n > k → f n ≤ C * g n
```

> **용어 정리**  
> - **상수 함수**(constant function): 입력이 무엇이든 항상 같은 값을 반환하는 함수. 예: `fun n => 12`  
> - **O(1)**: 입력 크기에 관계없이 연산 횟수가 일정한 복잡도. "상수 복잡도"라고도 한다.

### 예제: O(1) 증명 — 완전한 풀이

```lean
-- 상수 함수 12는 O(1)이다
-- 즉, fun n => 12 는 O(fun n => 1) 이다

theorem ex1_O_1 :
    IsBigO (fun _ => 12) (fun _ => 1) := by
  -- Step 1: 증인(witness) C = 12, k = 0을 선택한다
  use 12, 0
  -- Step 2: 임의의 n > 0에 대해 12 ≤ 12 * 1을 보인다
  intro n _hn
  -- 12 * 1 = 12이므로 자명하다
  omega
```

위 증명을 한 줄씩 뜯어보자:

| 줄 | 코드 | 의미 |
|---|------|------|
| 1 | `use 12, 0` | ∃ C k에서 C = 12, k = 0을 선택한다 |
| 2 | `intro n _hn` | "임의의 n"과 "n > 0이라는 가정"을 도입한다 |
| 3 | `omega` | 12 ≤ 12 * 1이 산술적으로 참임을 자동 증명한다 |

> **`omega` 전술**(tactic)이란?  
> `omega`는 자연수나 정수에 대한 **선형 부등식**을 자동으로 풀어주는 전술이다. "12 ≤ 12 * 1" 같은 간단한 산술 목표(goal)에 매우 유용하다. 비선형(곱, 제곱 등)이 포함된 부등식에는 `nlinarith`를 사용한다.

### 연습 6E.1: 괄호 채우기

**문제**: 다음 증명에서 빈칸(▢)을 채우시오.

```lean
-- "20은 O(1)이다"
theorem ex1_practice :
    IsBigO (fun _ => 20) (fun _ => 1) := by
  use ▢, ▢
  intro n _hn
  ▢
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem ex1_practice :
    IsBigO (fun _ => 20) (fun _ => 1) := by
  use 20, 0       -- C = 20, k = 0
  intro n _hn
  omega           -- 20 ≤ 20 * 1
```

**풀이 과정**:
- C = 20을 선택하면 20 ≤ 20 * 1 = 20이 성립한다.
- k = 0이면 모든 n > 0에 대해 성립하므로 충분하다.
- `omega`가 20 ≤ 20을 자동으로 증명한다.

</details>

---

## 6E.3 교재 연습문제 2번: 이중 루프의 Big-O

### 문제 원문

> 아래 알고리즘의 덧셈 횟수를 Big-O로 추정하라.
>
> ```
> t := 0
> for i := 1 to n
>     for j := 1 to n
>         t := t + i + j
> ```

### 풀이

**1단계**: 바깥 루프 `for i := 1 to n` → **n번** 반복

**2단계**: 안쪽 루프 `for j := 1 to n` → **n번** 반복

**3단계**: 루프 본문 `t := t + i + j`에서 덧셈은 **2번** 실행된다 (`t + i`에서 1번, 그 결과 `+ j`에서 1번).

**4단계**: 총 덧셈 횟수 = n × n × 2 = **2n²**

**5단계**: 2n²은 **O(n²)**이다.

> **왜 2n²이 O(n²)인가?**  
> Big-O 정의에 따르면, `f(n) = 2n²`이 `O(g(n))` = `O(n²)`이라는 것은:  
> ∃ C, k, ∀ n > k, 2n² ≤ C · n²  
> C = 2, k = 0을 선택하면: 2n² ≤ 2 · n² (항상 성립)  
> 따라서 2n² = O(n²)이다.

### Lean4 풀이: 완전한 예제

```lean
-- 연습문제 2: 이중 루프의 덧셈 횟수
def ops_ex2 (n : Nat) : Nat := 2 * n ^ 2

-- 2n²은 O(n²)
theorem ex2_O_n2 :
    IsBigO (fun n => 2 * n ^ 2) (fun n => n ^ 2) := by
  -- C = 2, k = 0
  use 2, 0
  intro n _hn
  -- 목표: 2 * n ^ 2 ≤ 2 * n ^ 2
  -- 이것은 자명하다 (≤ 는 반사적)
  le_refl
```

잠깐! `le_refl`은 `a ≤ a`를 증명하는 정리인데, 직접 적용하려면 `exact le_refl _`이나 `omega`를 사용해야 한다.

```lean
-- 수정된 증명
theorem ex2_O_n2 :
    IsBigO (fun n => 2 * n ^ 2) (fun n => n ^ 2) := by
  use 2, 0
  intro n _hn
  -- 목표: 2 * n ^ 2 ≤ 2 * (n ^ 2)
  -- 왼쪽과 오른쪽이 같으므로 omega로 해결
  omega
```

### 예제: 한 줄씩 따라가기

증명 상태(proof state)의 변화를 보자:

```
-- 초기 목표:
-- ⊢ IsBigO (fun n => 2 * n ^ 2) (fun n => n ^ 2)

-- `use 2, 0` 후:
-- ⊢ ∀ n > 0, 2 * n ^ 2 ≤ 2 * n ^ 2

-- `intro n _hn` 후:
-- n : Nat
-- _hn : n > 0
-- ⊢ 2 * n ^ 2 ≤ 2 * n ^ 2

-- `omega` 후:
-- (증명 완료!)
```

### 연습 6E.2: 괄호 채우기

**문제**: 다음 증명의 빈칸을 채우시오.

```lean
-- 3n²은 O(n²)
theorem ex2_practice :
    IsBigO (fun n => 3 * n ^ 2) (fun n => n ^ 2) := by
  use ▢, ▢
  intro n _hn
  ▢
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem ex2_practice :
    IsBigO (fun n => 3 * n ^ 2) (fun n => n ^ 2) := by
  use 3, 0      -- C = 3이면 3n² ≤ 3 · n²
  intro n _hn
  omega         -- 3 * n ^ 2 ≤ 3 * n ^ 2 (같으므로 자명)
```

</details>

### 연습 6E.3: sorry로 증명하기

**문제**: 다음 정리를 `sorry` 없이 증명하시오.

```lean
-- 5n² + 3n은 O(n²)
theorem ex2_challenge :
    IsBigO (fun n => 5 * n ^ 2 + 3 * n) (fun n => n ^ 2) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem ex2_challenge :
    IsBigO (fun n => 5 * n ^ 2 + 3 * n) (fun n => n ^ 2) := by
  use 8, 1
  intro n hn
  -- n ≥ 2이면 3n ≤ 3n² 이므로
  -- 5n² + 3n ≤ 5n² + 3n² = 8n²
  nlinarith [sq_nonneg n]
```

**풀이 과정**:
- n > 1 (즉 n ≥ 2)이면, 3n ≤ 3n² (왜냐하면 n ≤ n²)
- 따라서 5n² + 3n ≤ 5n² + 3n² = 8n²
- C = 8, k = 1을 선택한다
- `nlinarith`는 **비선형 산술**(nonlinear arithmetic) 전술로, `n²` 같은 제곱이 포함된 부등식도 처리한다

> **`nlinarith` vs `omega`**  
> - `omega`: **선형** 산술만 처리 (덧셈, 뺄셈, 상수 곱). `n²`이 나오면 실패할 수 있다.  
> - `nlinarith`: **비선형** 산술도 처리. 추가 힌트(`[sq_nonneg n]` 등)를 주면 더 강력하다.

</details>

---

## 6E.4 교재 연습문제 3번: 변하는 안쪽 루프 범위

### 문제 원문

> 아래 알고리즘에서 사용된 연산 횟수를 Big-O로 추정하라. 여기에서 연산은 비교나 곱셈이다. (**for** 루프의 조건을 검사하는 비교는 무시하라.)
>
> ```
> m := 0
> for i := 1 to n
>     for j := i + 1 to n
>         m := max(a_i * a_j, m)
> ```

### 풀이

이 문제는 앞의 문제와 다른 점이 있다. 안쪽 루프의 시작점이 `j = i + 1`이므로, **안쪽 루프의 반복 횟수가 i에 따라 변한다**는 것이다.

**1단계**: `i = 1`일 때, `j`는 2부터 n까지 → **(n - 1)번** 반복

**2단계**: `i = 2`일 때, `j`는 3부터 n까지 → **(n - 2)번** 반복

**3단계**: ...

**4단계**: `i = n - 1`일 때, `j`는 n부터 n까지 → **1번** 반복

**5단계**: `i = n`일 때, `j`는 n + 1부터 n까지 → **0번** 반복 (실행 안 됨)

따라서 총 연산 횟수는:

$$(n-1) + (n-2) + \cdots + 1 + 0 = \sum_{k=0}^{n-1} k = \frac{(n-1)n}{2}$$

이것은 유명한 **가우스 합 공식**이다. (n-1)n/2는 **O(n²)**이다.

> **가우스 합 공식**(Gauss's summation formula)  
> 1 + 2 + 3 + ... + m = m(m+1)/2  
> 위에서는 m = n - 1이므로: (n-1) + (n-2) + ... + 1 = (n-1)n/2

### Lean4 풀이

```lean
-- 연습문제 3: 변하는 안쪽 루프
-- 총 연산 횟수: (n-1)n/2

-- Nat에서 나눗셈은 내림 나눗셈이므로 주의해야 한다
-- n * (n - 1) / 2 로 표현

def ops_ex3 (n : Nat) : Nat := n * (n - 1) / 2

-- (n-1)n/2 ≤ n² 이므로 O(n²)
-- 왜? n(n-1)/2 = (n² - n)/2 ≤ n²/2 ≤ n²

theorem ex3_O_n2 :
    IsBigO ops_ex3 (fun n => n ^ 2) := by
  use 1, 0
  intro n _hn
  unfold ops_ex3
  -- 목표: n * (n - 1) / 2 ≤ 1 * n ^ 2
  -- n * (n - 1) / 2 ≤ n * (n - 1) ≤ n * n = n²
  have h1 : n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ 2
  have h2 : n * (n - 1) ≤ n * n := by
    apply Nat.mul_le_mul_left
    omega
  calc n * (n - 1) / 2
      ≤ n * (n - 1) := h1
    _ ≤ n * n := h2
    _ = n ^ 2 := by ring
```

### 예제: calc 전술 이해하기

위 증명에서 `calc`은 **계산 체인**(calculation chain)을 만드는 전술이다. 수학에서 "A ≤ B ≤ C ≤ D"처럼 부등식을 이어서 쓰는 것과 같다.

```lean
-- calc 블록의 구조:
calc n * (n - 1) / 2
    ≤ n * (n - 1) := h1        -- 첫 번째 부등식: 나눗셈하면 작아진다
  _ ≤ n * n := h2              -- 두 번째 부등식: n-1 ≤ n이므로
  _ = n ^ 2 := by ring         -- 마지막: n*n = n² (정의)
```

`_`는 "바로 앞의 값"을 나타낸다. 즉:
- 첫 줄: `n * (n-1) / 2 ≤ n * (n-1)`
- 둘째 줄: `n * (n-1) ≤ n * n`
- 셋째 줄: `n * n = n ^ 2`

Lean은 이 체인을 조합하여 `n * (n-1) / 2 ≤ n ^ 2`를 증명한다.

> **`calc` 전술**(tactic)이란?  
> 여러 단계의 등식(=)이나 부등식(≤, <)을 연결하여 최종 결론을 도출하는 전술이다. 수학 증명에서 "A = B ≤ C < D"와 같은 연쇄 논증을 그대로 코드로 옮길 수 있다.

### 연습 6E.4: 괄호 채우기

**문제**: 다음 증명의 빈칸을 채우시오.

```lean
-- n(n+1)/2 는 O(n²)
theorem ex3_practice :
    IsBigO (fun n => n * (n + 1) / 2) (fun n => n ^ 2) := by
  use ▢, ▢
  intro n _hn
  have h1 : n * (n + 1) / 2 ≤ n * (n + 1) := ▢
  have h2 : n * (n + 1) ≤ ▢ := by ▢
  calc n * (n + 1) / 2
      ≤ n * (n + 1) := h1
    _ ≤ ▢ := h2
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem ex3_practice :
    IsBigO (fun n => n * (n + 1) / 2) (fun n => n ^ 2) := by
  use 2, 0
  intro n _hn
  have h1 : n * (n + 1) / 2 ≤ n * (n + 1) := Nat.div_le_self _ 2
  have h2 : n * (n + 1) ≤ 2 * n ^ 2 := by nlinarith
  calc n * (n + 1) / 2
      ≤ n * (n + 1) := h1
    _ ≤ 2 * n ^ 2 := h2
```

**풀이 과정**:
- `Nat.div_le_self _ 2`: Lean4의 라이브러리 정리로, `a / b ≤ a`를 증명한다
- n(n+1) = n² + n ≤ 2n² (n ≥ 1일 때)이므로 C = 2
- `nlinarith`가 n² + n ≤ 2n²를 자동 증명

</details>

---

## 6E.5 교재 연습문제 4번: while 루프의 Big-O

### 문제 원문

> 아래 알고리즘에서 사용된 연산 횟수를 Big-O로 추정하라. 여기에서 연산은 덧셈이나 곱셈이다. (**while** 루프의 조건을 검사하는 비교는 무시하라.)
>
> ```
> i := 1
> t := 0
> while i ≤ n
>     t := t + i
>     i := 2i
> ```

### 풀이

이 알고리즘은 특별하다. `i`가 매번 **2배**가 되기 때문이다.

**추적해보기**: `i`의 값 변화
- 처음: i = 1
- 1번째 반복 후: i = 2
- 2번째 반복 후: i = 4
- 3번째 반복 후: i = 8
- ...
- k번째 반복 후: i = 2^k

루프는 `i ≤ n`인 동안 계속된다. 따라서 루프가 멈추는 조건은 `2^k > n`, 즉 `k > log₂ n`이다.

그러므로 루프는 약 **⌊log₂ n⌋ + 1**번 반복한다. 각 반복에서 덧셈 1번(`t + i`)과 곱셈 1번(`2i`)이 실행되므로, 총 연산 횟수는 약 **2(⌊log₂ n⌋ + 1)**이다.

이것은 **O(log n)**이다.

> **로그**(logarithm)란?  
> `log₂ n`은 "2를 몇 번 곱해야 n이 되는가?"라는 질문의 답이다.  
> 예: log₂ 8 = 3 (2³ = 8), log₂ 16 = 4 (2⁴ = 16)  
> Big-O에서는 로그의 밑(base)이 중요하지 않다. `log₂ n`과 `log₁₀ n`은 상수배 차이이므로, 둘 다 `O(log n)`이다.

### Lean4 풀이

```lean
-- 연습문제 4: while 루프에서 i가 매번 2배
-- 연산 횟수: 약 2 * (⌊log₂ n⌋ + 1)

-- Lean4에서 로그는 Nat.log로 계산한다
#eval Nat.log 2 8    -- 결과: 3
#eval Nat.log 2 16   -- 결과: 4
#eval Nat.log 2 100  -- 결과: 6

def ops_ex4 (n : Nat) : Nat := 2 * (Nat.log 2 n + 1)

-- 2(log₂ n + 1)은 O(log n)
-- C = 4, k = 1로 잡으면 충분하다 (n ≥ 2일 때 log₂ n ≥ 1)
```

> **`Nat.log`란?**  
> Lean4의 `Nat.log b n`은 밑(base)이 `b`인 `n`의 로그를 **자연수로 내림한 값**을 반환한다.  
> `Nat.log 2 8 = 3`, `Nat.log 2 7 = 2`이다.

### 연습 6E.5: #eval로 확인하기

**문제**: 다음 `#eval` 결과를 예측하시오.

```lean
#eval Nat.log 2 1     -- ▢
#eval Nat.log 2 2     -- ▢
#eval Nat.log 2 3     -- ▢
#eval Nat.log 2 4     -- ▢
#eval Nat.log 2 32    -- ▢
#eval Nat.log 2 1000  -- ▢
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval Nat.log 2 1     -- 0  (2⁰ = 1)
#eval Nat.log 2 2     -- 1  (2¹ = 2)
#eval Nat.log 2 3     -- 1  (2¹ ≤ 3 < 2²)
#eval Nat.log 2 4     -- 2  (2² = 4)
#eval Nat.log 2 32    -- 5  (2⁵ = 32)
#eval Nat.log 2 1000  -- 9  (2⁹ = 512 ≤ 1000 < 2¹⁰ = 1024)
```

`Nat.log b n`은 `b^k ≤ n`을 만족하는 **가장 큰 k**를 반환한다.

</details>

---

## 6E.6 교재 연습문제 5번: 3.1절 연습문제 16 알고리즘

### 문제 원문

> 3.1절 연습문제 16의 알고리즘을 사용하면 **n개의 자연수의 수열에서 가장 작은 자연수를 찾는 데** 비교를 몇 번 하는가?

이 알고리즘은 기본적으로 **최솟값 찾기** 알고리즘이다. 최댓값 찾기와 동일한 구조를 갖는다.

```
-- 최솟값 찾기 의사 코드
min_val := a₁
for i := 2 to n
    if a_i < min_val then
        min_val := a_i
return min_val
```

### 풀이

루프는 `i = 2`부터 `i = n`까지, 총 **(n - 1)번** 반복한다. 각 반복에서 비교(`a_i < min_val`)가 **1번** 실행된다.

따라서 비교 횟수 = **n - 1**이다. 이것은 **O(n)**이다.

### Lean4 풀이

```lean
-- 최솟값 찾기의 비교 횟수
def comparisons_min (n : Nat) : Nat := n - 1

-- n - 1 은 O(n)
theorem min_O_n :
    IsBigO (fun n => n - 1) (fun n => n) := by
  use 1, 0
  intro n _hn
  -- 목표: n - 1 ≤ 1 * n
  omega
```

`omega`는 `n - 1 ≤ n`을 즉시 증명한다. (자연수에서 항상 성립)

### 연습 6E.6: sorry로 증명하기

**문제**: 다음 정리를 증명하시오.

```lean
-- 2n - 5 는 O(n)
theorem ex5_practice :
    IsBigO (fun n => 2 * n - 5) (fun n => n) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem ex5_practice :
    IsBigO (fun n => 2 * n - 5) (fun n => n) := by
  use 2, 0
  intro n _hn
  -- 2n - 5 ≤ 2n (Nat에서 뺄셈은 0 이하로 내려가지 않으므로)
  omega
```

**참고**: Lean4의 `Nat` 타입에서 뺄셈은 음수가 될 수 없다. 따라서 `2 * 1 - 5 = 0` (결과가 음수면 0이 된다). 이 성질 덕분에 `2 * n - 5 ≤ 2 * n`은 항상 성립한다.

</details>

---

## 6E.7 중첩 루프의 Big-O: 일반 규칙

연습문제 6~12번을 풀기 전에, 중첩 루프에서 Big-O를 추정하는 일반 규칙을 정리하자.

### 규칙 1: 단순 중첩 루프

```
for i := 1 to n
    for j := 1 to n
        [상수 시간 연산]
```

→ 연산 횟수: **n × n = n²** → **O(n²)**

### 규칙 2: 안쪽 루프 범위가 바깥에 의존

```
for i := 1 to n
    for j := 1 to i
        [상수 시간 연산]
```

→ 연산 횟수: 1 + 2 + 3 + ... + n = **n(n+1)/2** → **O(n²)**

### 규칙 3: 삼중 루프

```
for i := 1 to n
    for j := 1 to n
        for k := 1 to n
            [상수 시간 연산]
```

→ 연산 횟수: **n³** → **O(n³)**

### 규칙 4: 로그 루프

```
i := 1
while i ≤ n
    [상수 시간 연산]
    i := 2 * i
```

→ 반복 횟수: **⌊log₂ n⌋ + 1** → **O(log n)**

### 규칙 5: 순차 실행

두 개의 연속 루프가 있으면:
```
for i := 1 to n: [O(n) 연산]
for j := 1 to n²: [O(n²) 연산]
```

→ 총: O(n) + O(n²) = **O(n²)** (더 큰 것이 지배)

### Lean4로 규칙 표현

```lean
-- 규칙 5의 Lean4 증명: O(n) + O(n²) = O(n²)
-- 즉, n + n²은 O(n²)

theorem sum_rule_example :
    IsBigO (fun n => n + n ^ 2) (fun n => n ^ 2) := by
  use 2, 1
  intro n hn
  -- n > 1이면 n ≤ n² 이므로
  -- n + n² ≤ n² + n² = 2n²
  nlinarith [sq_nonneg n]
```

이 증명에서 핵심은 `n ≤ n²` (n ≥ 1일 때)라는 사실이다. 이로부터 `n + n² ≤ n² + n² = 2n²`이 따라나온다.

---

## 6E.8 교재 연습문제 6: 삽입 정렬의 의사 코드 분석

### 문제 원문 (a)

> 임의의 길이인 실수의 리스트의 처음 네 항을 오름차 순으로 삽입 정렬하는 알고리즘을 의사 코드로 기술하라.

### 풀이 (a)

삽입 정렬(insertion sort)은 리스트의 원소를 하나씩 꺼내서 이미 정렬된 부분에 올바른 위치에 삽입하는 알고리즘이다.

처음 네 항만 정렬하므로:

```
-- 리스트: a₁, a₂, a₃, a₄, a₅, ..., aₙ
-- 처음 4개만 정렬

for j := 2 to min(4, n)
    key := a_j
    i := j - 1
    while i > 0 and a_i > key
        a_{i+1} := a_i
        i := i - 1
    a_{i+1} := key
```

### 풀이 (b): 비교 횟수의 시간복잡도

비교 횟수를 분석하자.
- j = 2일 때: 최대 1번 비교
- j = 3일 때: 최대 2번 비교
- j = 4일 때: 최대 3번 비교

최악의 경우 총 비교 횟수 = 1 + 2 + 3 = **6번**.

4는 상수이므로, 이 알고리즘의 시간복잡도는 **O(1)**이다.

```lean
-- 연습문제 6: 처음 4개만 삽입 정렬
-- 최악의 경우 비교 횟수: 1 + 2 + 3 = 6 (상수)
-- 따라서 O(1)

def ops_ex6 : Nat := 6

theorem ex6_O_1 :
    IsBigO (fun _ => 6) (fun _ => 1) := by
  use 6, 0
  intro n _hn
  omega
```

---

## 6E.9 교재 연습문제 7~9: #eval로 연산 횟수 확인

연습문제 7~9번은 실제 값을 계산하여 확인하는 문제이다. Lean4의 `#eval`을 사용하면 된다.

### 연습문제 7: 32개 원소에서 선형 탐색 vs 이진 탐색

```lean
-- 32개 원소의 리스트에서 원소를 찾을 때
-- 선형 탐색: 최악의 경우 32번 비교
-- 이진 탐색: 최악의 경우 ⌊log₂ 32⌋ + 1 = 6번 비교

#eval (32 : Nat)               -- 선형 탐색: 32
#eval Nat.log 2 32 + 1         -- 이진 탐색: 6

-- 이진 탐색이 훨씬 빠르다!
```

### 연습 6E.7: 계산 문제

**문제**: 다음을 `#eval`로 계산하시오.

```lean
-- n = 64일 때
-- (a) 선형 탐색 최악의 경우 비교 횟수: ▢
#eval (64 : Nat)

-- (b) 이진 탐색 최악의 경우 비교 횟수: ▢
#eval Nat.log 2 64 + 1

-- (c) 버블 정렬 최악의 경우 비교 횟수: ▢
#eval 64 * 63 / 2

-- (d) 삽입 정렬 최악의 경우 비교 횟수: ▢
#eval 64 * 63 / 2
```

<details>
<summary>💡 답 보기</summary>

```lean
#eval (64 : Nat)            -- (a) 64
#eval Nat.log 2 64 + 1      -- (b) 7 (log₂ 64 = 6, +1 = 7)
#eval 64 * 63 / 2           -- (c) 2016
#eval 64 * 63 / 2           -- (d) 2016
```

**해석**:
- 선형 탐색: 64번이면 끝
- 이진 탐색: 7번이면 끝 (매번 범위가 반으로 줄어듦)
- 버블 정렬: 2016번 비교 (O(n²)이 체감됨!)
- 삽입 정렬: 최악의 경우 2016번 (버블 정렬과 동일한 차수)

</details>

### 연습문제 8: x^(2^k)를 구하는 곱셈 횟수

```lean
-- 실수 x와 양의 정수 k가 주어졌을 때
-- x부터 시작해서 x^(2^k)를 구하는 데 필요한 곱셈 횟수

-- 방법: x → x² → x⁴ → x⁸ → ... → x^(2^k)
-- 각 단계에서 "이전 결과를 제곱" = 곱셈 1번
-- 총 k번의 곱셈이 필요

#eval (1 : Nat)   -- k=1: x → x² (1번)
#eval (2 : Nat)   -- k=2: x → x² → x⁴ (2번)
#eval (3 : Nat)   -- k=3: x → x² → x⁴ → x⁸ (3번)
```

### 연습문제 9: 비트 문자열에서 1의 개수

```lean
-- 비트 문자열이 주어졌을 때, 각 비트가 1인지 아닌지를
-- 조사해서 1의 개수를 알아내는 알고리즘의 비교 횟수

-- n비트 문자열 → n번 비교 (각 비트를 한 번씩 검사)
-- Big-O 추정: O(n)

def bit_count_comparisons (n : Nat) : Nat := n

theorem ex9_O_n :
    IsBigO bit_count_comparisons (fun n => n) := by
  use 1, 0
  intro n _hn
  unfold bit_count_comparisons
  omega
```

---

## 6E.10 교재 연습문제 10: 비트 AND 연산 횟수

### 문제 원문

> 다음의 알고리즘으로 비트 문자열 S에 있는 1의 개수를 알아낼 수 있음을 증명하라.
>
> ```
> procedure bit_count(S: bit string)
> count := 0
> while S ≠ 0
>     count := count + 1
>     S := S ∧ (S − 1)
> return count
> ```

### 풀이

이 알고리즘의 핵심 아이디어는 `S ∧ (S - 1)` 연산이다. 이 연산은 S의 **가장 오른쪽에 있는 1비트를 제거**한다.

예를 들어:
- S = 1010₂ → S - 1 = 1001₂ → S ∧ (S-1) = 1000₂ (마지막 1이 사라짐)
- S = 1000₂ → S - 1 = 0111₂ → S ∧ (S-1) = 0000₂ (마지막 1이 사라짐)

따라서 while 루프는 S에 있는 **1의 개수**만큼 반복한다.

(b) **비트별 AND 횟수**: 루프가 `count`번(= 1의 개수) 반복하고, 각 반복에서 AND 1번이므로, 총 AND 횟수 = **1의 개수**이다. 최악의 경우(모든 비트가 1) n비트 문자열에서 AND는 **n번** 실행된다.

```lean
-- 비트 count 알고리즘의 AND 연산 횟수
-- 최악의 경우: n비트 모두 1 → n번

def bit_count_and_ops (n : Nat) : Nat := n  -- 최악의 경우

-- O(n)
theorem ex10_O_n :
    IsBigO bit_count_and_ops (fun n => n) := by
  use 1, 0
  intro n _hn
  unfold bit_count_and_ops
  omega
```

### 연습 6E.8: 비트 연산 이해하기

**문제**: 다음에서 `S ∧ (S - 1)` 연산의 결과를 계산하시오 (2진법으로).

```
(a) S = 0110 → S - 1 = ▢ → S ∧ (S-1) = ▢
(b) S = 1111 → S - 1 = ▢ → S ∧ (S-1) = ▢
(c) S = 1000 → S - 1 = ▢ → S ∧ (S-1) = ▢
(d) S = 0001 → S - 1 = ▢ → S ∧ (S-1) = ▢
```

<details>
<summary>💡 답 보기</summary>

```
(a) S = 0110 → S - 1 = 0101 → S ∧ (S-1) = 0100
    (가장 오른쪽 1비트 '10'에서 '1'이 사라짐)

(b) S = 1111 → S - 1 = 1110 → S ∧ (S-1) = 1110
    (가장 오른쪽 '1'이 사라짐)

(c) S = 1000 → S - 1 = 0111 → S ∧ (S-1) = 0000
    (유일한 '1'이 사라짐)

(d) S = 0001 → S - 1 = 0000 → S ∧ (S-1) = 0000
    (유일한 '1'이 사라짐)
```

**패턴**: `S ∧ (S-1)`은 항상 S에서 **가장 오른쪽 1비트 하나를 제거**한다.

</details>

---

## 6E.11 교재 연습문제 11: 서로소 부분집합 찾기

### 문제 원문

> {1, 2, ..., n}의 n개의 부분집합 S₁, S₂, ..., Sₙ이 있다. 이들 중 **서로소**(disjoint)인 부분집합이 있는지를 찾아내는 역지 알고리즘을 설명하라.

### 풀이

**서로소**(disjoint)란 두 집합의 **교집합이 공집합**인 것이다: `S_i ∩ S_j = ∅`

**역지 알고리즘**(brute-force algorithm): 모든 쌍 (Sᵢ, Sⱼ)를 검사하여 교집합이 비어 있는지 확인한다.

```
for i := 1 to n
    for j := i + 1 to n
        -- S_i와 S_j가 서로소인지 검사
        is_disjoint := true
        for each element k in S_i
            if k ∈ S_j then
                is_disjoint := false
                break
        if is_disjoint then
            return (S_i, S_j)
return "없음"
```

### 비교 횟수 분석 (b)

- 쌍의 수: n(n-1)/2 (연습문제 3과 같은 구조)
- 각 쌍에서 최대 n번 비교 (S_i의 각 원소가 S_j에 있는지)
- 최악의 총 비교 횟수: n(n-1)/2 × n = **n²(n-1)/2**

이것은 **O(n³)**이다.

```lean
-- 서로소 부분집합 찾기: 비교 횟수
def ops_disjoint (n : Nat) : Nat := n ^ 2 * (n - 1) / 2

-- O(n³)
theorem ex11_O_n3 :
    IsBigO ops_disjoint (fun n => n ^ 3) := by
  use 1, 0
  intro n _hn
  unfold ops_disjoint
  -- n²(n-1)/2 ≤ n²·n = n³
  have h1 : n ^ 2 * (n - 1) / 2 ≤ n ^ 2 * (n - 1) := Nat.div_le_self _ 2
  have h2 : n ^ 2 * (n - 1) ≤ n ^ 3 := by nlinarith
  linarith
```

---

## 6E.12 교재 연습문제 12: 최소 항 행렬 알고리즘

### 문제 원문

> n개의 정수수열 a₁, a₂, ..., aₙ을 입력받고 행렬 M = {mᵢⱼ}를 출력하는 다음 알고리즘을 고려해 보자. j ≥ i이면 mᵢⱼ는 정수수열 aᵢ, aᵢ₊₁, ..., aⱼ의 최솟값이고, 그렇지 않으면 mᵢⱼ = 0이다.

```
initialize M so that m_ij = a_i if j ≥ i and m_ij = 0 otherwise
for i := 1 to n
    for j := i + 1 to n
        for k := i + 1 to j
            m_ij := min(m_ij, a_k)
return M
```

### 풀이 (a): O(n³)번의 비교

삼중 루프를 분석하자.

바깥 루프 `i`: 1부터 n까지 (n번)  
중간 루프 `j`: i+1부터 n까지 (변동)  
안쪽 루프 `k`: i+1부터 j까지 (변동)

각 반복에서 `min` 비교가 1번 실행된다. 총 비교 횟수를 정확히 계산하려면 삼중 합을 구해야 하지만, Big-O 추정만 하면 충분하다.

모든 루프의 범위가 n 이하이므로, 상한은 **n × n × n = n³**이다. 따라서 이 알고리즘은 **O(n³)**이다.

```lean
-- 연습문제 12(a): 삼중 루프 → O(n³)
theorem ex12a_O_n3 :
    IsBigO (fun n => n ^ 3) (fun n => n ^ 3) := by
  use 1, 0
  intro n _hn
  omega
```

### 풀이 (b): Ω(n³)번의 비교

**O(n³)일 뿐만 아니라 Ω(n³)**이기도 하다는 것을 보여야 한다. 즉, 실제로 비교가 n³에 비례하게 많이 일어난다는 것이다.

힌트: 바깥 두 루프에서 `i ≤ n/4`이고 `j ≥ 3n/4`인 경우만 세어도, 안쪽 루프가 `n/2`번 이상 반복한다. 이런 (i, j) 쌍이 약 (n/4)² = n²/16개 있으므로, 총 비교 횟수 ≥ (n²/16)(n/2) = n³/32이다.

따라서 비교 횟수는 **Θ(n³)**이다.

```lean
-- Θ(n³)이므로 O(n³)이면서 Ω(n³)
-- 이것은 곧 비교가 정확히 n³ 차수임을 의미한다
```

---

## 6E.13 종합 연습

### 연습 6E.9: Big-O 매칭 (괄호 채우기)

**문제**: 각 함수에 대해 가장 적절한 Big-O를 선택하시오.

```
f(n)                          | Big-O
------------------------------|--------
(a) 7n + 12                  | O(▢)
(b) 3n² + 5n + 2             | O(▢)
(c) n³ + 100n² + 9999        | O(▢)
(d) 5                         | O(▢)
(e) 2 log₂ n + 7             | O(▢)
(f) n log₂ n + n             | O(▢)
```

<details>
<summary>💡 답 보기</summary>

```
(a) 7n + 12                  | O(n)
(b) 3n² + 5n + 2             | O(n²)
(c) n³ + 100n² + 9999        | O(n³)
(d) 5                         | O(1)
(e) 2 log₂ n + 7             | O(log n)
(f) n log₂ n + n             | O(n log n)
```

**규칙**: Big-O는 **최고차 항**(leading term)에 의해 결정된다. 계수(7, 3, 100 등)와 하위 항은 무시한다.

</details>

### 연습 6E.10: Lean4 증명 종합 (sorry)

**문제**: 다음을 모두 증명하시오.

```lean
-- (1) 7n + 12는 O(n)
theorem practice_1 :
    IsBigO (fun n => 7 * n + 12) (fun n => n) := by
  sorry

-- (2) n² + 100은 O(n²)
theorem practice_2 :
    IsBigO (fun n => n ^ 2 + 100) (fun n => n ^ 2) := by
  sorry

-- (3) 3n³ + n은 O(n³)
theorem practice_3 :
    IsBigO (fun n => 3 * n ^ 3 + n) (fun n => n ^ 3) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
-- (1) 7n + 12는 O(n)
theorem practice_1 :
    IsBigO (fun n => 7 * n + 12) (fun n => n) := by
  use 19, 1
  intro n hn
  -- n > 1이면 12 ≤ 12n이므로 7n + 12 ≤ 7n + 12n = 19n
  omega

-- (2) n² + 100은 O(n²)
theorem practice_2 :
    IsBigO (fun n => n ^ 2 + 100) (fun n => n ^ 2) := by
  use 101, 1
  intro n hn
  -- n > 1이면 100 ≤ 100n² 이므로
  -- n² + 100 ≤ n² + 100n² = 101n²
  nlinarith [sq_nonneg n]

-- (3) 3n³ + n은 O(n³)
theorem practice_3 :
    IsBigO (fun n => 3 * n ^ 3 + n) (fun n => n ^ 3) := by
  use 4, 1
  intro n hn
  -- n > 1이면 n ≤ n³이므로
  -- 3n³ + n ≤ 3n³ + n³ = 4n³
  nlinarith [sq_nonneg n]
```

**C 선택 팁**: 하위 항의 계수를 최고차 항의 계수에 더하면 된다.
- (1): 7 + 12 = 19 (12 ≤ 12n이므로 실제로는 C = 7 + 12 = 19면 충분)
- (2): 1 + 100 = 101
- (3): 3 + 1 = 4

</details>

---

## 6E.14 도전 문제

### 도전 6E.1: Big-O의 비(非)성립 증명

**문제**: n²은 **O(n)이 아님**을 증명하시오.

```lean
-- n²이 O(n)이 아닌 것의 Lean4 표현:
-- ¬ IsBigO (fun n => n ^ 2) (fun n => n)

theorem challenge_not_O_n :
    ¬ IsBigO (fun n => n ^ 2) (fun n => n) := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem challenge_not_O_n :
    ¬ IsBigO (fun n => n ^ 2) (fun n => n) := by
  -- 부정(¬)을 증명하려면 intro로 가정을 도입한 뒤 모순을 유도한다
  intro ⟨C, k, h⟩
  -- h : ∀ n > k, n² ≤ C * n
  -- n = C + k + 1을 대입하면 모순이 생긴다
  have h_spec := h (C + k + 1) (by omega)
  -- h_spec : (C + k + 1)² ≤ C * (C + k + 1)
  -- 그런데 (C + k + 1)² = (C + k + 1)(C + k + 1) > C(C + k + 1)
  -- 왜냐하면 C + k + 1 > C이기 때문이다
  nlinarith [sq_nonneg k]
```

**풀이 설명**:
1. `intro ⟨C, k, h⟩`: "n²이 O(n)이라고 **가정**한다" → C, k, h를 얻는다
2. `h (C + k + 1)`: C와 k보다 충분히 큰 값을 대입하여 모순을 유도한다
3. `nlinarith`: (C+k+1)² > C·(C+k+1)임을 자동 증명하여 `h_spec`과 모순

이것은 **귀류법**(proof by contradiction)의 변형이다. "만약 O(n)이라면 어떤 C가 존재해야 하는데, 그 C보다 큰 입력을 넣으면 모순이 생긴다"는 논증이다.

</details>

### 도전 6E.2: 알고리즘 비교

**문제**: 두 알고리즘의 연산 횟수가 각각 `100n`과 `n²`일 때, `n`이 얼마부터 첫 번째 알고리즘이 더 효율적인지 Lean4로 보이시오.

```lean
-- n > 100이면 100n < n²

theorem alg_comparison :
    ∀ n : Nat, n > 100 → 100 * n < n ^ 2 := by
  sorry
```

<details>
<summary>💡 답 보기</summary>

```lean
theorem alg_comparison :
    ∀ n : Nat, n > 100 → 100 * n < n ^ 2 := by
  intro n hn
  -- n > 100이면 n² = n * n > 100 * n
  -- 왜냐하면 n > 100이므로
  nlinarith
```

즉, n = 101부터 100n 알고리즘이 더 빠르다. `#eval`로 확인:

```lean
#eval 100 * 101       -- 10100
#eval 101 ^ 2         -- 10201
-- 10100 < 10201 ✓

#eval 100 * 100       -- 10000
#eval 100 ^ 2         -- 10000
-- 10000 = 10000 (같음, 아직 역전 안 됨)
```

</details>

---

## 6E.15 전술 요약

### 이 장에서 사용한 전술

| 전술 | 용도 | 예 |
|------|------|-----|
| `use` | ∃ 증인 제시 | `use 3, 0` (C=3, k=0) |
| `intro` | ∀ 변수 / → 가정 도입 | `intro n hn` |
| `omega` | 선형 자연수 산술 | `n - 1 ≤ n` |
| `nlinarith` | 비선형 산술 | `n + n² ≤ 2n²` |
| `calc` | 계산 체인 | A ≤ B ≤ C 연결 |
| `unfold` | 정의 펼치기 | `unfold ops_ex3` |
| `have` | 보조 사실 도입 | `have h : A := ...` |
| `linarith` | 선형 실수 산술 | 가설에서 목표 도출 |
| `ring` | 대수적 등식 | `n * n = n ^ 2` |

### 이 장에서 사용한 라이브러리 정리

| 정리 | 의미 |
|------|------|
| `Nat.div_le_self a b` | a / b ≤ a |
| `sq_nonneg n` | 0 ≤ n² |
| `Nat.mul_le_mul_left` | a ≤ b → k*a ≤ k*b |

---

## 6E.16 핵심 요약

1. **루프 횟수 세기**: 각 루프의 반복 횟수를 곱하여(중첩 루프) 또는 더하여(순차 루프) 총 연산 횟수를 계산한다.

2. **Big-O 증명 패턴**: `use C, k` → `intro n hn` → `omega` 또는 `nlinarith`

3. **핵심 부등식**: n ≥ 1이면 n ≤ n², 1 ≤ n이면 상수 ≤ 상수 × n

4. **계수는 무시**: Big-O에서 `3n²`과 `100n²`은 모두 `O(n²)`.

5. **#eval 활용**: Lean4에서 실제 값을 계산하여 직관을 확인할 수 있다.

---

## 다음 편 예고

**제6-F편**에서는:
- 교재 연습문제 13~22 (호너의 방법, 비트 연산 시간, 입력 크기 변화에 따른 시간 변화)
- **행렬 곱의 복잡도**와 행렬 체인 곱
- **알고리즘 패러다임**: 역지 알고리즘, 분할정복, 탐욕 알고리즘
- **P vs NP** 문제의 직관적 이해

를 다룬다.

---

**(끝)**
