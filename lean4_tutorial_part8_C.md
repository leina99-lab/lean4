# Lean4 완전 정복 가이드 — 제8-C편

## **강 귀납법**(Strong Induction)과 **순서화**(Well-Ordering) — 완전 정복

> **교재**: Kenneth H. Rosen, "Discrete Mathematics and Its Applications" 8판, 5.2절  
> **참고**: 『Mathematics in Lean』 Chapter 5.2–5.3 (Induction and Recursion, Infinitely Many Primes)  
> **선수 학습**: 제8-A편 (수학적 귀납법 원리), 제8-B편 (부등식·나누어짐)

---

## 8C.0 이 장의 목표

이 장에서 배울 내용은 다음과 같다:

1. **강 귀납법**(strong induction)이란 무엇이며, 보통 귀납법과 어떻게 다른가
2. 강 귀납법은 **언제** 필요한가 — "바로 이전 단계"만으로는 부족한 경우
3. Lean4에서 강 귀납법을 사용하는 방법 — `Nat.strong_induction_on`
4. 교재 예제: **우표 문제**(postage stamp), **소인수 분해**(prime factorization)
5. **순서화 성질**(well-ordering property)과 귀납법의 관계
6. 강 귀납법 ↔ 보통 귀납법 — 사실은 **동치**이다!
7. 『Mathematics in Lean』의 `exists_prime_factor` 증명 완전 해부

---

## 8C.1 왜 강 귀납법이 필요한가?

### 8C.1.1 보통 귀납법의 한계

8-A편에서 배운 **보통 귀납법**(ordinary/weak induction)을 떠올려 보자:

> **보통 귀납법**: P(0)이 참이고, 모든 k에 대해 P(k) → P(k+1)이면, 모든 n에 대해 P(n)이 참이다.

핵심은 **귀납적 단계**에서 "바로 이전 단계 P(k)만 가정"한다는 것이다. 즉, k번째 계단에서 (k+1)번째 계단으로 올라갈 때, k번째에 서 있다는 사실 **하나만** 사용할 수 있다.

그런데 어떤 증명에서는 이것만으로는 부족하다. 예를 들어 보자:

> **문제**: 2 이상의 모든 자연수는 소수들의 곱으로 표현할 수 있다.

n = 12를 증명하려면, 12 = 4 × 3이므로 4와 3 각각이 소수의 곱임을 알아야 한다. 그런데 4는 12 바로 이전 수(11)가 아니라 **훨씬 작은 수**이다! P(11)만 알아서는 P(12)를 증명할 수 없다. P(4)와 P(3) **모두** 필요하다.

이런 상황에서 필요한 것이 바로 **강 귀납법**이다.

### 8C.1.2 강 귀납법의 아이디어 — 역사 도서관 비유

보통 귀납법이 "사다리 오르기"라면, 강 귀납법은 **"역사 도서관"**에 비유할 수 있다.

> 🏛️ **역사 도서관 비유**:  
> 도서관에 1번부터 무한히 많은 책이 순서대로 꽂혀 있다고 하자.  
> - **보통 귀납법**: "바로 앞 책(k번)의 내용을 알면, 다음 책(k+1번)을 쓸 수 있다"  
> - **강 귀납법**: "**1번부터 k번까지의 모든 책 내용**을 알면, (k+1)번 책을 쓸 수 있다"

강 귀납법에서는 (k+1)번째를 증명할 때, 이전의 **모든** 단계 — P(1), P(2), ..., P(k) — 를 가정으로 사용할 수 있다. 이것이 "강(strong)"이라 불리는 이유이다.

### 8C.1.3 공식 정의

교재(Rosen 5.2절)에 나오는 **강 귀납법**(strong induction)의 원리는 다음과 같다:

> **강 귀납법의 원리**(Principle of Strong Induction):  
> P(n)을 양의 정수 n에 대한 명제라 하자. 만약:
>
> **[P(1) ∧ P(2) ∧ ... ∧ P(k)] → P(k+1)**
>
> 이 모든 양의 정수 k에 대해 성립하면, P(n)은 모든 양의 정수 n에 대해 참이다.

좀 더 정확하게 쓰면:

$$\left[\forall k \geq 1, \left(\forall j,\; 1 \leq j \leq k \implies P(j)\right) \implies P(k+1)\right] \implies \forall n \geq 1,\; P(n)$$

잠깐, **기본 단계**(basis step)는 어디로 갔을까? 사실 k = 0일 때를 생각하면, "1번부터 0번까지의 모든 j에 대해 P(j)가 참"이라는 가정은 **공진**(vacuously true)이다 — 해당하는 j가 하나도 없기 때문이다! 따라서 k = 0인 경우의 귀납적 단계가 자동으로 P(1)의 증명을 요구한다. 즉, **기본 단계가 귀납적 단계에 흡수**되는 것이다.

> 💡 **핵심 포인트**: 강 귀납법은 형식적으로는 기본 단계가 별도로 필요 없다.  
> 하지만 실전에서는 가장 작은 경우(들)를 먼저 따로 확인하는 것이 명확하다.

### 8C.1.4 보통 귀납법 vs 강 귀납법 비교표

| 구분 | **보통 귀납법**(weak) | **강 귀납법**(strong) |
|------|---------------------|---------------------|
| 기본 단계 | P(b) 증명 | (형식적으로 불필요, 실전에서는 확인) |
| 귀납적 가설 | P(k) **하나만** 가정 | P(b), P(b+1), ..., P(k) **모두** 가정 |
| 귀납적 단계 | P(k) → P(k+1) | [P(b)∧...∧P(k)] → P(k+1) |
| Lean4 전술 | `induction n with` | `induction n using Nat.strong_induction_on with` |
| 별명 | 약한 귀납법 | 완전 귀납법(complete induction), 과정 귀납법(course-of-values induction) |
| 힘의 차이 | 동일! (동치) | 동일! (동치) |

마지막 줄이 놀랍지 않은가? **보통 귀납법과 강 귀납법은 사실 동치**이다. 어느 하나로 증명할 수 있는 것은 다른 하나로도 증명할 수 있다. 다만 **강 귀납법이 더 편리한 상황**이 있을 뿐이다. 이에 대해서는 8C.6절에서 자세히 다루겠다.

---

## 8C.2 Lean4에서 강 귀납법 사용하기

### 8C.2.1 `Nat.strong_induction_on`이란?

『Mathematics in Lean』에서는 강 귀납법을 다음과 같이 소개한다:

> Lean에서 이 원리는 `Nat.strong_induction_on`이라 불리며, `using` 키워드를 통해  
> `induction` 전술에게 이것을 사용하라고 알려줄 수 있다.  
> **주목할 점**: 강 귀납법을 사용하면 **기본 단계가 없다** — 일반적인 귀납적 단계에 흡수된다.

### 8C.2.2 문법

```lean
-- 보통 귀납법 (복습)
theorem weak_example (n : Nat) : P n := by
  induction n with
  | zero => sorry      -- 기본 단계: P(0)
  | succ n ih => sorry  -- 귀납적 단계: ih : P(n) ⊢ P(n+1)

-- 강 귀납법 ✨
theorem strong_example (n : Nat) : P n := by
  induction n using Nat.strong_rec_on with
  | _ n ih => sorry
  -- ih : ∀ m, m < n → P m
  -- 즉, "n보다 작은 모든 m에 대해 P(m)이 참"
```

차이를 자세히 살펴보자:

| 보통 귀납법 | 강 귀납법 |
|-----------|-----------|
| `induction n with` | `induction n using Nat.strong_rec_on with` |
| `ih : P(n)` | `ih : ∀ m, m < n → P m` |
| "바로 이전" 하나만 | "**n보다 작은 모든 것**"을 사용 가능 |
| 목표: `P(n+1)` | 목표: `P(n)` |
| 기본/귀납 두 가지 분리 | **하나의 목표**만 (기본 단계 흡수) |

> ⚠️ **Lean 버전 참고**: Mathlib 버전에 따라 `Nat.strong_induction_on`, `Nat.strong_rec_on`,  
> `Nat.strongRecOn` 등 이름이 다를 수 있다. 핵심은 동일하다:  
> "**n보다 작은 모든 값에서 성립한다고 가정하고, n에서 증명하라**"

### 8C.2.3 ih의 사용법

강 귀납법에서 `ih`의 타입은:

```
ih : ∀ m, m < n → P m
```

이것은 "n보다 작은 **어떤** m에 대해서든 P(m)이 참"이라는 뜻이다. 사용할 때는:

```lean
-- m이 n보다 작다는 것을 증명해야 한다
have h1 : some_value < n := by ...
have h2 : P some_value := ih some_value h1
```

보통 귀납법에서는 `ih`를 그냥 쓰면 되었지만, 강 귀납법에서는 **두 가지**를 제공해야 한다:
1. 사용하고 싶은 **구체적인 값** m
2. 그 값이 **n보다 작다**는 증명

이것은 마치 역사 도서관에서 "몇 번 책을 꺼내겠습니다"라고 말하고, "그 번호가 현재 번호보다 작다"는 것을 보여주는 것과 같다.

### 8C.2.4 첫 번째 예제: 기본 구조 익히기

강 귀납법의 가장 단순한 예를 보자. 사실 보통 귀납법으로도 충분히 증명할 수 있지만, 구조를 익히기 위한 것이다.

> **예제**: 모든 자연수 n ≥ 1에 대하여 n ≥ 1이다. (자명하지만 구조 연습!)

```lean
-- 강 귀납법의 기본 골격 연습
theorem trivial_strong (n : Nat) (hn : n ≥ 1) : n ≥ 1 := by
  exact hn  -- 물론 이건 자명하다!

-- 진짜 강 귀납법 구조를 보려면:
theorem all_pos_ge_one (n : Nat) : n = 0 ∨ n ≥ 1 := by
  induction n using Nat.strong_rec_on with
  | _ n ih =>
    -- ih : ∀ m < n, m = 0 ∨ m ≥ 1
    -- 목표: n = 0 ∨ n ≥ 1
    cases n with
    | zero => left; rfl
    | succ k => right; omega
```

여기서 핵심은 **`induction n using Nat.strong_rec_on with`** 라인이다. 이것이 강 귀납법을 발동시키는 주문이다.

---

## 8C.3 교재 예제 1: 2 이상의 모든 자연수는 소수의 곱

### 8C.3.1 문제

> **정리**(Rosen 5.2절, 예제 1): 2 이상의 모든 자연수는 **소수**(prime)이거나 **소수들의 곱**으로 표현할 수 있다.

이것은 **산술의 기본 정리**(Fundamental Theorem of Arithmetic)의 "존재" 부분이다.

### 8C.3.2 왜 강 귀납법이 필요한가?

보통 귀납법으로 시도해 보자:
- P(k)가 참이라고 가정: "k는 소수이거나 소수들의 곱이다"
- P(k+1)을 보여야 한다: "k+1은 소수이거나 소수들의 곱이다"

만약 k+1이 소수라면 끝이다. 하지만 k+1이 합성수라면? k+1 = a × b (1 < a, b < k+1)로 쓸 수 있다. 이때 a와 b는 k+1보다 작지만, **반드시 k인 것은 아니다**! 예를 들어 k+1 = 15라면 a = 3, b = 5인데, P(14)만 알아서는 P(3)과 P(5)를 알 수 없다.

그래서 **강 귀납법**이 필요하다: P(2), P(3), ..., P(k) **전부** 가정하면, a와 b 모두에 대해 가설을 적용할 수 있다.

### 8C.3.3 수학적 증명

P(n)을 "n은 소수이거나 소수들의 곱으로 쓸 수 있다"라 하자.

**강 귀납법 가설**: 2 ≤ j ≤ k인 모든 j에 대해 P(j)가 참이라고 가정하자.

P(k+1)을 증명한다:
- **경우 1**: k+1이 소수이면 → P(k+1)은 자명하게 참이다.
- **경우 2**: k+1이 합성수이면 → k+1 = a × b (2 ≤ a, b ≤ k)로 쓸 수 있다.
  - a ≤ k이고 a ≥ 2이므로, 강 귀납 가설에 의하여 P(a)가 참이다.
  - b ≤ k이고 b ≥ 2이므로, 강 귀납 가설에 의하여 P(b)가 참이다.
  - 따라서 a와 b 모두 소수들의 곱이므로, k+1 = a × b도 소수들의 곱이다.

**Q.E.D.** ∎

### 8C.3.4 Lean4 구현 — `exists_prime_factor`

『Mathematics in Lean』에는 이와 관련된 멋진 정리가 있다: "2 이상의 모든 자연수는 소인수를 갖는다."

먼저, 보조 도구인 `two_le`를 살펴보자:

```lean
-- 0도 아니고 1도 아닌 자연수는 2 이상이다
theorem two_le {m : Nat} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m with
  | zero => contradiction     -- m = 0이면 h0과 모순
  | succ m =>
    cases m with
    | zero => contradiction   -- m = 1이면 h1과 모순
    | succ m =>
      -- m = succ (succ m), 즉 m ≥ 2
      repeat apply Nat.succ_le_succ
      apply Nat.zero_le
```

이 정리는 "0도 1도 아닌 자연수"를 다루는 데 꼭 필요한 도구이다. `cases`를 두 번 사용하여 m = 0과 m = 1을 각각 모순으로 처리한 뒤, 나머지 경우에 2 ≤ m을 보이는 패턴이다.

이제 핵심 정리:

```lean
-- 2 이상의 모든 자연수는 소인수를 갖는다
theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) :
    ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · -- n 자체가 소수인 경우
    use n, np           -- p = n, n은 소수이고 n ∣ n
  · -- n이 소수가 아닌 경우: 강 귀납법 사용!
    induction n using Nat.strong_rec_on with
    | _ n ih =>
      -- ih : ∀ m < n, 2 ≤ m → ¬m.Prime → ∃ p, p.Prime ∧ p ∣ m
      -- np : ¬n.Prime
      -- h  : 2 ≤ n
      rw [Nat.prime_def_lt] at np
      push_neg at np
      -- np가 이제 "∃ m, 2 ≤ m ∧ m < n ∧ m ∣ n" 형태가 됨
      rcases np h with ⟨m, mltn, mdvdn, mne1⟩
      -- m은 n의 비자명 약수: m < n, m ∣ n, m ≠ 1
      have : m ≠ 0 := by
        intro mz
        rw [mz, zero_dvd_iff] at mdvdn
        linarith   -- n = 0이면 2 ≤ n과 모순
      have mgt2 : 2 ≤ m := two_le this mne1
      by_cases mp : m.Prime
      · -- m이 소수이면: m이 찾던 소인수!
        use m, mp
      · -- m도 소수가 아니면: 강 귀납 가설 사용
        -- m < n이므로 ih를 m에 적용할 수 있다
        rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
        -- p는 m의 소인수: p.Prime ∧ p ∣ m
        use p, pp
        -- p ∣ m 이고 m ∣ n 이므로 p ∣ n
        exact pdvd.trans mdvdn
```

### 8C.3.5 증명 해부 — 단계별 분석

이 증명에서 일어나는 일을 아주 천천히 따라가 보자:

**1단계: 소수인지 아닌지 분류** (`by_cases np : n.Prime`)
```
     n
    / \
 소수?  합성수?
  ↓       ↓
 끝!    계속...
```
n이 소수이면 `use n, np`로 바로 끝난다. (n 자체가 소인수이므로.)

**2단계: 합성수이면 비자명 약수 m을 찾기**

`Nat.prime_def_lt`는 소수의 정의를 "비자명 약수가 없다"로 풀어주고, `push_neg`로 부정을 안쪽으로 밀어넣으면, "비자명 약수 m이 존재한다"가 된다.

**3단계: m에 대해 다시 소수 판별** (`by_cases mp : m.Prime`)
- m이 소수이면 → m이 찾던 소인수이다.
- m도 소수가 아니면 → **강 귀납 가설** `ih`를 사용한다!

**4단계: 강 귀납 가설 적용** (`ih m mltn mgt2 mp`)

여기가 핵심이다. `ih`에 세 가지 정보를 전달한다:
- `m`: 적용할 값
- `mltn`: m < n (강 귀납법의 핵심 조건!)
- `mgt2`: 2 ≤ m
- `mp`: ¬m.Prime

그러면 `ih`가 "m의 소인수 p"를 돌려준다.

**5단계: 나누어짐의 전이성** (`pdvd.trans mdvdn`)

p ∣ m 이고 m ∣ n이면 p ∣ n이다. 이것이 `Dvd.dvd.trans`의 핵심이다.

### 8C.3.6 중간 괄호 채우기 연습

아래 코드에서 `[???]` 부분을 채워 보자:

```lean
theorem exists_prime_factor_practice {n : Nat} (h : 2 ≤ n) :
    ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use [???], [???]           -- n 자체가 소수인 경우
  · induction n using Nat.strong_rec_on with
    | _ n ih =>
      rw [Nat.prime_def_lt] at np
      push_neg at np
      rcases np h with ⟨m, mltn, mdvdn, mne1⟩
      have mne0 : m ≠ 0 := by
        intro mz; rw [mz, [???]] at mdvdn; [???]
      have mgt2 : 2 ≤ m := [???] mne0 mne1
      by_cases mp : m.Prime
      · use m, [???]
      · rcases ih [???] mltn mgt2 mp with ⟨p, pp, pdvd⟩
        use p, pp
        exact [???].trans mdvdn
```

<details>
<summary>정답 보기</summary>

```lean
theorem exists_prime_factor_practice {n : Nat} (h : 2 ≤ n) :
    ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  · induction n using Nat.strong_rec_on with
    | _ n ih =>
      rw [Nat.prime_def_lt] at np
      push_neg at np
      rcases np h with ⟨m, mltn, mdvdn, mne1⟩
      have mne0 : m ≠ 0 := by
        intro mz; rw [mz, zero_dvd_iff] at mdvdn; linarith
      have mgt2 : 2 ≤ m := two_le mne0 mne1
      by_cases mp : m.Prime
      · use m, mp
      · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
        use p, pp
        exact pdvd.trans mdvdn
```

</details>

---

## 8C.4 교재 예제 2: 우표 문제 (Postage Stamp Problem)

### 8C.4.1 문제

> **정리**(Rosen 5.2절): 12센트 이상의 모든 우편 요금은 **4센트 우표**와 **5센트 우표**만으로 낼 수 있다.

즉, n ≥ 12이면 4a + 5b = n을 만족하는 음이 아닌 정수 a, b가 존재한다.

### 8C.4.2 왜 강 귀납법이 자연스러운가?

n = 28을 생각해 보자. 28센트를 만들려면 예를 들어 24 + 4 = 28, 즉 24센트에 4센트 우표 하나를 추가하면 된다. 그런데 P(24)를 사용하려면? P(27) — 바로 이전 — 만으로는 부족하다. **P(n-4)**가 필요하다!

더 일반적으로, P(k+1)을 증명하기 위해 **P(k-3)** (즉, 4를 빼는 것)을 사용해야 할 수 있다. 이것은 보통 귀납법의 "바로 이전만 사용"을 넘어선다.

> 💡 사실 이 문제는 보통 귀납법으로도 풀 수 있다(기본 단계를 4개 잡으면). 하지만 강 귀납법이 훨씬 자연스럽다.

### 8C.4.3 수학적 증명 (강 귀납법)

P(n)을 "n센트를 4센트와 5센트 우표로 낼 수 있다"라 하자.

**기본 단계** (여러 개가 필요하다):
- P(12): 12 = 4 × 3 ✓
- P(13): 13 = 4 × 2 + 5 × 1 ✓
- P(14): 14 = 4 × 1 + 5 × 2 ✓
- P(15): 15 = 5 × 3 ✓

**귀납적 단계**: n ≥ 16일 때, P(12), P(13), ..., P(n-1)이 모두 참이라 가정하자.

n ≥ 16이므로 n - 4 ≥ 12이다. 따라서 강 귀납 가설에 의하여 P(n-4)가 참이다. 즉, (n-4)센트를 4센트와 5센트 우표로 낼 수 있다. 여기에 **4센트 우표 하나를 추가**하면 n센트를 낼 수 있다!

형식적으로: n - 4 = 4a + 5b이면 n = 4(a+1) + 5b. ∎

### 8C.4.4 Lean4 구현

```lean
-- 우표 문제: n ≥ 12이면 4a + 5b = n인 a, b가 존재
theorem postage_stamp (n : Nat) (h : 12 ≤ n) :
    ∃ a b : Nat, 4 * a + 5 * b = n := by
  induction n using Nat.strong_rec_on with
  | _ n ih =>
    -- ih : ∀ m < n, 12 ≤ m → ∃ a b, 4 * a + 5 * b = m
    interval_cases n  -- n = 12, 13, 14, 15를 자동 처리
    -- 이렇게 하면 12 ≤ n ≤ ... 범위의 각 경우를 생성
    -- (실제로는 omega나 decide로 처리 가능)
    all_goals first
      | exact ⟨3, 0, by ring⟩    -- 12 = 4×3
      | exact ⟨2, 1, by ring⟩    -- 13 = 4×2 + 5
      | exact ⟨1, 2, by ring⟩    -- 14 = 4 + 5×2
      | exact ⟨0, 3, by ring⟩    -- 15 = 5×3
      | -- n ≥ 16인 일반적 경우
        have h4 : n - 4 < n := by omega
        have h12 : 12 ≤ n - 4 := by omega
        rcases ih (n - 4) h4 h12 with ⟨a, b, hab⟩
        exact ⟨a + 1, b, by omega⟩
```

> ⚠️ **참고**: 실제 Lean4에서 위 코드가 정확히 동작하려면 세부 조정이 필요할 수 있다. 핵심 패턴을 보여주기 위한 의사코드이다.

더 실용적인 접근은 다음과 같다:

```lean
-- 간결한 버전: omega의 힘을 빌리기
theorem postage_stamp_v2 (n : Nat) (h : 12 ≤ n) :
    ∃ a b : Nat, 4 * a + 5 * b = n := by
  -- 핵심 아이디어: n을 4로 나눈 나머지로 경우를 나눈다
  -- n ≡ 0 (mod 4): n = 4 × (n/4)
  -- n ≡ 1 (mod 4): n = 4 × ((n-5)/4) + 5
  -- n ≡ 2 (mod 4): n = 4 × ((n-10)/4) + 5 × 2
  -- n ≡ 3 (mod 4): n = 4 × ((n-15)/4) + 5 × 3
  -- 이것은 사실 강 귀납법 없이도 가능하다!
  -- 하지만 강 귀납법 버전이 더 직관적이다.
  sorry  -- 독자에게 맡김 (연습!)
```

### 8C.4.5 sorry 연습

다음 증명을 완성해 보자. `sorry`를 모두 채우면 된다:

```lean
theorem postage_16 : ∃ a b : Nat, 4 * a + 5 * b = 16 := by
  -- 16 = 4 × 4 + 5 × 0
  sorry

theorem postage_17 : ∃ a b : Nat, 4 * a + 5 * b = 17 := by
  -- 17 = 4 × 3 + 5 × 1
  sorry

theorem postage_23 : ∃ a b : Nat, 4 * a + 5 * b = 23 := by
  -- 23 = 4 × 2 + 5 × 3
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
theorem postage_16 : ∃ a b : Nat, 4 * a + 5 * b = 16 := by
  exact ⟨4, 0, by ring⟩

theorem postage_17 : ∃ a b : Nat, 4 * a + 5 * b = 17 := by
  exact ⟨3, 1, by ring⟩

theorem postage_23 : ∃ a b : Nat, 4 * a + 5 * b = 23 := by
  exact ⟨2, 3, by ring⟩
```

</details>

---

## 8C.5 교재 예제 3: 소수의 무한성 (응용)

### 8C.5.1 정리

> **정리** (유클리드): 모든 자연수 n보다 큰 소수가 존재한다. (즉, 소수는 무한히 많다.)

이것은 `exists_prime_factor`를 활용하는 아름다운 응용이다.

### 8C.5.2 증명 아이디어

n!+1을 생각하자. n!+1 ≥ 2이므로 소인수 p가 존재한다(8C.3절의 정리에 의해).

만약 p ≤ n이면:
- p는 n!을 나눈다 (p ≤ n이면 p는 1 × 2 × ... × n의 인수이므로)
- p는 n!+1도 나눈다 (가정)
- 따라서 p는 (n!+1) - n! = 1을 나눈다 → **모순!** (p ≥ 2이므로)

따라서 p > n이다. ∎

### 8C.5.3 Lean4 구현 (Mathematics in Lean)

```lean
theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  -- n! + 1은 2 이상이다
  have h : 2 ≤ Nat.factorial n + 1 := by
    have : 0 < Nat.factorial n := Nat.factorial_pos n
    omega
  -- 소인수 p가 존재한다 (강 귀납법으로 증명된 정리!)
  rcases exists_prime_factor h with ⟨p, pp, pdvd⟩
  -- p > n임을 보인다
  refine ⟨p, ?_, pp⟩
  show p > n
  by_contra ple
  push_neg at ple
  -- p ≤ n이면 p | n!
  have h1 : p ∣ Nat.factorial n := by
    exact Nat.dvd_factorial.mpr ⟨pp.pos, ple⟩
  -- p | (n! + 1)이고 p | n! 이면 p | 1
  have h2 : p ∣ 1 := by
    exact (Nat.dvd_sub' pdvd h1).mp (by omega)
  -- 하지만 p ≥ 2이므로 p | 1은 불가능
  show False
  exact Nat.Prime.one_lt pp |>.not_le (Nat.le_of_dvd one_pos h2)
```

여기서 `exists_prime_factor`는 8C.3절에서 **강 귀납법으로 증명한 정리**이다! 이처럼 강 귀납법으로 증명한 결과가 다른 정리의 핵심 재료가 된다.

### 8C.5.4 핵심 전술 정리

| 전술/정리 | 역할 |
|---------|------|
| `Nat.factorial_pos n` | 0 < n! |
| `Nat.dvd_factorial` | p ∣ n! ↔ (0 < p ∧ p ≤ n) |
| `Nat.dvd_sub'` | a ∣ b → a ∣ c → a ∣ (b - c) |
| `Nat.Prime.one_lt` | p가 소수이면 1 < p |
| `exists_prime_factor` | 2 ≤ n이면 소인수가 존재 (강 귀납법!) |

---

## 8C.6 보통 귀납법 ↔ 강 귀납법: 동치 증명

### 8C.6.1 놀라운 사실

교재(Rosen 5.2절)는 다음을 언급한다:

> "사실 귀납법, 강 귀납법, 순서화 성질은 모두 동일한 법칙이다(연습문제 41, 42, 43에서 보여주듯이). 즉, 각각의 유효성은 다른 두 개의 유효성으로부터 나올 수 있다."

즉, **보통 귀납법으로 증명할 수 있는 것은 강 귀납법으로도 증명할 수 있고, 그 역도 성립**한다.

### 8C.6.2 직관적 이해

**강 → 보통** (자명): 강 귀납법은 보통 귀납법보다 "더 많이 가정"하므로, 보통 귀납법으로 증명 가능한 것은 당연히 강 귀납법으로도 가능하다. (가정이 더 많으니까.)

**보통 → 강** (트릭이 필요): 핵심 아이디어는 **명제를 바꾸는 것**이다!

P(n)을 강 귀납법으로 증명하고 싶다고 하자. 새로운 명제를 정의한다:

> Q(n) ≡ "P(1) ∧ P(2) ∧ ... ∧ P(n)"

즉, Q(n)은 "1부터 n까지 **전부** 참"이라는 뜻이다. 이제 Q(n)에 **보통 귀납법**을 적용하면:

- **기본 단계**: Q(1), 즉 P(1)을 보인다.
- **귀납적 단계**: Q(k) → Q(k+1), 즉 [P(1) ∧ ... ∧ P(k)] → [P(1) ∧ ... ∧ P(k) ∧ P(k+1)]

두 번째 단계에서 P(k+1)만 새로 보이면 되는데, 이때 P(1), ..., P(k)를 **모두** 가정으로 사용할 수 있다 — 이것이 바로 강 귀납법의 가설과 동일하다!

```lean
-- 개념적 증명 (의사코드)
-- 강 귀납법이 보통 귀납법과 동치임을 보이는 아이디어

-- Q(n) = ∀ j ≤ n, P(j)
-- Q에 보통 귀납법을 적용하면:
-- 기본: Q(0), 즉 ∀ j ≤ 0, P(j)  -- j = 0인 경우만
-- 귀납: Q(k) → Q(k+1)
--       ∀ j ≤ k, P(j)  →  ∀ j ≤ k+1, P(j)
--       이때 j ≤ k인 경우는 가설에서, j = k+1인 경우만 새로 증명
--       P(k+1)을 증명할 때 P(1)...P(k) 모두 사용 가능! = 강 귀납법
```

### 8C.6.3 Lean4에서의 의미

Lean4에서는 이 동치성이 이미 내장되어 있다. `Nat.strong_rec_on`은 `Nat.rec` (보통 재귀)로부터 구현되어 있다. 즉, Lean의 핵심 논리에는 보통 귀납법만 있고, 강 귀납법은 그로부터 **유도된 것**이다.

```lean
-- Lean4의 내부: Nat.strong_rec_on은 보통 재귀로 구현됨
-- (실제 구현은 복잡하지만, 개념적으로는:)

-- strong_rec_on을 보통 rec으로 구현하는 아이디어:
-- h를 "∀ m < n, P m"이라 하면
-- aux(n) := ∀ m < n, P m  -- 이것을 보통 귀납법으로 증명
-- aux(0)     : 공진 (vacuously true)
-- aux(n+1)   : aux(n)을 알고, P(n)도 알면 됨
--              P(n)은 h에 aux(n)을 전달해서 얻음
```

> 🎓 **교훈**: 수학에서 "더 강한 도구"처럼 보이는 것이 실제로는 기본 도구와 동치인 경우가 많다. 강 귀납법은 보통 귀납법의 **편리한 포장**이지, 본질적으로 더 강한 것이 아니다.

---

## 8C.7 순서화 성질 (Well-Ordering Property)

### 8C.7.1 정의

> **순서화 성질**(Well-Ordering Property):  
> 양의 정수의 **공집합이 아닌** 모든 부분집합은 **최솟값**(least element)을 갖는다.

예를 들어:
- {3, 7, 1, 5}의 최솟값은 1이다.
- 모든 소수의 집합 {2, 3, 5, 7, 11, ...}의 최솟값은 2이다.
- 홀수의 집합 {1, 3, 5, 7, ...}의 최솟값은 1이다.

이것은 너무 당연해 보이지만, 실수(ℝ)에서는 성립하지 않는다! 예를 들어 양의 실수의 집합 {x ∈ ℝ : x > 0}에는 최솟값이 없다. (0.1, 0.01, 0.001, ... 어디까지나 더 작은 양수를 찾을 수 있으므로.)

### 8C.7.2 순서화 ↔ 귀납법의 관계

교재에 따르면, 다음 세 가지는 **모두 동치**이다:

1. **수학적 귀납법의 원리** (보통 귀납법)
2. **강 귀납법의 원리**
3. **순서화 성질**

하나를 공리로 받아들이면 나머지 둘을 증명할 수 있다!

### 8C.7.3 순서화 → 강 귀납법 (증명 스케치)

강 귀납법이 **실패한다고** 가정하자. 즉, 어떤 명제 P에 대해 강 귀납법의 조건이 성립하지만 P(n₀)이 거짓인 n₀이 존재한다고 하자.

S = {n ∈ ℕ : P(n)이 거짓}이라 하면, S는 공집합이 아니다(n₀ ∈ S).

순서화 성질에 의하여 S에는 최솟값 m이 존재한다. m보다 작은 모든 자연수 j에 대해서는 P(j)가 참이다(그렇지 않으면 m이 최솟값이 아니게 되므로).

하지만 강 귀납법의 조건에 의하면, m보다 작은 모든 j에 대해 P(j)가 참이면 P(m)도 참이어야 한다. **모순!**

따라서 강 귀납법은 타당하다. ∎

### 8C.7.4 Lean4에서의 순서화

Lean4의 자연수 타입 `Nat`에는 순서화 성질이 내장되어 있다:

```lean
-- Nat.find: 조건을 만족하는 최소 자연수를 찾는다
-- (DecidablePred가 필요)
#check @Nat.find  -- {p : Nat → Prop} → [DecidablePred p] → (∃ n, p n) → Nat

-- 예시: 10보다 큰 최소 소수 찾기
example : Nat.find ⟨11, by norm_num⟩ = 11 := by
  sorry  -- 구체적인 계산 필요

-- Nat.find_spec: Nat.find가 실제로 조건을 만족함
#check @Nat.find_spec  -- 찾은 값이 조건을 만족

-- Nat.find_min: Nat.find보다 작은 값은 조건을 만족하지 않음
#check @Nat.find_min   -- ∀ m < Nat.find, ¬p m
```

이 `Nat.find`가 바로 순서화 성질의 Lean4 버전이다. "조건을 만족하는 자연수가 존재하면, 최소인 것을 찾아준다"는 것이다.

---

## 8C.8 강 귀납법의 전형적 패턴 정리

지금까지의 내용을 정리하면, 강 귀납법을 사용할 때 다음 패턴을 따르면 된다:

### 패턴 1: 분해(decomposition) — 합성수 → 약수

```
P(n)을 증명하려면:
1. n이 "단순한" 경우(소수 등) → 직접 증명
2. n이 "복합적" 경우 → n = a ○ b로 분해
3. a < n, b < n이므로 강 귀납 가설로 P(a), P(b) 얻기
4. P(a)와 P(b)로부터 P(n) 도출
```

**Lean4 스켈레톤**:
```lean
theorem decomp_pattern (n : Nat) (h : 2 ≤ n) : P n := by
  induction n using Nat.strong_rec_on with
  | _ n ih =>
    by_cases simple : is_simple n
    · -- 단순한 경우 직접 처리
      sorry
    · -- 복합적 경우: 분해
      obtain ⟨a, b, ha, hb, hab⟩ := decompose n simple
      -- ha : a < n, hb : b < n
      have pa := ih a ha (condition_a)
      have pb := ih b hb (condition_b)
      -- pa와 pb로부터 P(n) 도출
      sorry
```

### 패턴 2: 뒤돌아보기(look-back) — n-k 사용

```
P(n)을 증명하려면:
1. 기본 단계: n이 작은 경우 여러 개를 직접 확인
2. 일반 경우: P(n-k)로부터 P(n)을 도출 (k > 1)
```

**Lean4 스켈레톤**:
```lean
theorem lookback_pattern (n : Nat) (h : b ≤ n) : P n := by
  induction n using Nat.strong_rec_on with
  | _ n ih =>
    -- 기본 단계들
    interval_cases n
    · sorry  -- n = b
    · sorry  -- n = b+1
    -- ... 필요한 만큼
    -- 일반 단계
    · have prev : n - k < n := by omega
      have hprev : b ≤ n - k := by omega
      have := ih (n - k) prev hprev
      sorry  -- 이전 결과로부터 P(n) 도출
```

### 패턴 3: 귀류법(contradiction) — 순서화 활용

```
P(n)이 모든 n에 대해 참임을 보이려면:
1. P(n₀)이 거짓인 n₀이 있다고 가정 (귀류법)
2. 반례 집합의 최솟값 m을 취한다 (순서화 성질)
3. m보다 작은 모든 값에서 P가 참임을 이용하여 P(m)도 참임을 보임
4. 모순!
```

---

## 8C.9 새로운 전술 총정리

### 8C.9.1 이번 편에서 배운 것들

| 전술/개념 | 용도 | 예시 |
|---------|------|------|
| `induction n using Nat.strong_rec_on` | 강 귀납법 발동 | "n보다 작은 모든 값에서 가정" |
| `ih m h_lt` | 강 귀납 가설 적용 | m < n인 m에 대해 P(m) 얻기 |
| `by_cases` | 경우 분리 | 소수/합성수, 기본/일반 |
| `rcases ... with ⟨..⟩` | 존재 명제 분해 | `∃ x, P x`에서 x와 증명 추출 |
| `push_neg` | 부정 안쪽으로 밀기 | `¬∀ → ∃ ¬` |
| `Dvd.dvd.trans` | 나누어짐의 전이성 | a∣b ∧ b∣c → a∣c |
| `two_le` | 0 ≠ m ∧ 1 ≠ m → 2 ≤ m | 자연수 하한 처리 |
| `interval_cases` | 유한 범위 자동 분리 | n이 12~15인 각 경우 |
| `Nat.find` | 순서화 성질(최솟값 찾기) | 조건 만족하는 최소 자연수 |
| `Nat.factorial_pos` | 0 < n! | 팩토리얼의 양수성 |
| `Nat.dvd_factorial` | p ∣ n! ↔ (0 < p ∧ p ≤ n) | 소수와 팩토리얼 관계 |

### 8C.9.2 보통 귀납법 vs 강 귀납법 전술 비교

```lean
-- ═══════════════════════════════════════════
-- 보통 귀납법
-- ═══════════════════════════════════════════
theorem weak (n : Nat) : P n := by
  induction n with
  | zero =>
    -- ⊢ P 0
    sorry
  | succ n ih =>
    -- ih : P n
    -- ⊢ P (n + 1)
    sorry

-- ═══════════════════════════════════════════
-- 강 귀납법
-- ═══════════════════════════════════════════
theorem strong (n : Nat) : P n := by
  induction n using Nat.strong_rec_on with
  | _ n ih =>
    -- ih : ∀ m, m < n → P m
    -- ⊢ P n
    sorry
```

---

## 8C.10 연습 세트

### 연습 8C.1: 소인수 존재 (직접 버전)

다음을 `sorry` 없이 완성하라. 힌트: `exists_prime_factor`의 구조를 참고하되, 간략화한 버전이다.

```lean
-- 6 이상의 모든 짝수는 2보다 큰 약수를 가진다
theorem even_gt_six_has_factor (n : Nat) (h1 : 6 ≤ n) (h2 : 2 ∣ n) :
    ∃ d : Nat, 2 ≤ d ∧ d < n ∧ d ∣ n := by
  sorry
```

<details>
<summary>힌트</summary>

d = 2를 사용하라. 2 ≤ 2, 2 < n (n ≥ 6이므로), 2 ∣ n (가정)이다.

</details>

<details>
<summary>정답 보기</summary>

```lean
theorem even_gt_six_has_factor (n : Nat) (h1 : 6 ≤ n) (h2 : 2 ∣ n) :
    ∃ d : Nat, 2 ≤ d ∧ d < n ∧ d ∣ n := by
  exact ⟨2, le_refl 2, by omega, h2⟩
```

</details>

---

### 연습 8C.2: 우표 문제 구체적 계산

다음 각각에 대해 `a`와 `b`의 구체적 값을 찾아 증명을 완성하라:

```lean
theorem stamp_20 : ∃ a b : Nat, 4 * a + 5 * b = 20 := by
  sorry

theorem stamp_27 : ∃ a b : Nat, 4 * a + 5 * b = 27 := by
  sorry

theorem stamp_31 : ∃ a b : Nat, 4 * a + 5 * b = 31 := by
  sorry
```

<details>
<summary>정답 보기</summary>

```lean
theorem stamp_20 : ∃ a b : Nat, 4 * a + 5 * b = 20 := ⟨5, 0, by ring⟩
-- 또는 ⟨0, 4, by ring⟩

theorem stamp_27 : ∃ a b : Nat, 4 * a + 5 * b = 27 := ⟨3, 3, by ring⟩

theorem stamp_31 : ∃ a b : Nat, 4 * a + 5 * b = 31 := ⟨4, 3, by ring⟩
```

</details>

---

### 연습 8C.3: 강 귀납법 구조 연습

다음 강 귀납법 증명의 `[???]`를 채워라:

```lean
-- 모든 자연수 n ≥ 1에 대해 n은 1 이상이다 (자명하지만 구조 연습!)
theorem ge_one_strong (n : Nat) (h : 1 ≤ n) : 1 ≤ n := by
  induction n using [???] with
  | _ n ih =>
    -- ih : ∀ m, m < n → 1 ≤ m → 1 ≤ m
    -- 이 경우는 자명하다
    exact [???]
```

<details>
<summary>정답 보기</summary>

```lean
theorem ge_one_strong (n : Nat) (h : 1 ≤ n) : 1 ≤ n := by
  induction n using Nat.strong_rec_on with
  | _ n ih =>
    exact h
```

(물론 이 예제는 `exact h`로 끝나므로 강 귀납법이 필요 없다. 구조를 익히기 위한 연습이다.)

</details>

---

### 연습 8C.4: 피보나치와 강 귀납법

피보나치 수열은 F(0) = 0, F(1) = 1, F(n) = F(n-1) + F(n-2)로 정의된다.

다음을 증명하라: 모든 n ≥ 1에 대해 F(n) ≥ 1

```lean
-- 피보나치 정의
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

-- 강 귀납법이 자연스러운 이유:
-- F(n+2) = F(n+1) + F(n)에서 F(n+1)과 F(n) 둘 다 필요!
-- 보통 귀납법에서는 F(n+1)만 가정할 수 있다.
theorem fib_pos (n : Nat) (h : 1 ≤ n) : 1 ≤ fib n := by
  sorry
```

<details>
<summary>힌트</summary>

강 귀납법을 사용하여 n = 1, n = 2를 기본 단계로 처리하고, n ≥ 3인 경우 fib(n) = fib(n-1) + fib(n-2)에서 두 항 모두에 강 귀납 가설을 적용하라.

</details>

<details>
<summary>정답 보기</summary>

```lean
theorem fib_pos (n : Nat) (h : 1 ≤ n) : 1 ≤ fib n := by
  induction n using Nat.strong_rec_on with
  | _ n ih =>
    match n, h with
    | 1, _ => simp [fib]       -- fib 1 = 1 ≥ 1
    | 2, _ => simp [fib]       -- fib 2 = 1 ≥ 1
    | n + 3, _ =>
      simp [fib]
      -- fib(n+3) = fib(n+2) + fib(n+1)
      have h1 : 1 ≤ fib (n + 2) := ih (n + 2) (by omega) (by omega)
      have h2 : 1 ≤ fib (n + 1) := ih (n + 1) (by omega) (by omega)
      omega
```

</details>

---

### 연습 8C.5 (도전): 이진 표현

> **정리**: 모든 양의 정수는 서로 다른 2의 거듭제곱의 합으로 표현할 수 있다.

이것은 사실 모든 양의 정수의 **이진 표현**(binary representation)이 존재한다는 것이다!

힌트: 강 귀납법을 사용하라. n이 짝수이면 n = 2 × (n/2)이고, n/2에 강 귀납 가설을 적용한다. n이 홀수이면 n = 2 × ((n-1)/2) + 1이고, (n-1)/2에 강 귀납 가설을 적용한다.

```lean
-- 이것은 형식적으로 정확히 표현하기 어려우므로
-- 비형식적 증명만 작성해 보자:

-- P(n) = "n은 서로 다른 2의 거듭제곱의 합으로 표현 가능"
-- 강 귀납법:
-- n = 1: 1 = 2⁰ ✓
-- n > 1:
--   n이 짝수: n = 2k, k < n, 강 귀납 가설로 P(k) 참
--     k = 2^a₁ + ... + 2^aₘ이면 n = 2^(a₁+1) + ... + 2^(aₘ+1)
--   n이 홀수: n = 2k + 1, k < n, 강 귀납 가설로 P(k) 참
--     k = 2^a₁ + ... + 2^aₘ이면 n = 2^(a₁+1) + ... + 2^(aₘ+1) + 2⁰
--     (2⁰은 사용되지 않았으므로 서로 다름 유지)
```

<details>
<summary>Lean4 스케치 (완전한 증명은 고급)</summary>

```lean
-- 이 증명은 Finset과 비트 연산이 필요하여 상당히 복잡하다.
-- 핵심 아이디어만 Lean4 스타일로 보여준다:

-- Nat.bits는 이미 Lean4/Mathlib에 이진 표현을 다루는 함수가 있다.
-- #check Nat.bits  -- Nat → List Bool

-- 사실 Lean4의 Nat 자체가 내부적으로 이진 표현을 사용한다!
-- 따라서 이 정리는 Lean의 기본 설계에 이미 내장되어 있다고 할 수 있다.
```

</details>

---

## 8C.11 핵심 요약 — 한눈에 보기

```
╔═══════════════════════════════════════════════════════════╗
║                    강 귀납법 핵심 정리                       ║
╠═══════════════════════════════════════════════════════════╣
║                                                           ║
║  보통 귀납법:  P(k)  ────→  P(k+1)                        ║
║               하나만                                       ║
║                                                           ║
║  강 귀납법:   P(1)∧P(2)∧...∧P(k) ────→ P(k+1)            ║
║               전부!                                        ║
║                                                           ║
║  Lean4:  induction n using Nat.strong_rec_on              ║
║          ih : ∀ m, m < n → P m                            ║
║                                                           ║
║  사용법:  ih m (m_lt_n의_증명)                              ║
║                                                           ║
║  ⚡ 보통 ↔ 강 ↔ 순서화: 모두 동치!                         ║
║                                                           ║
║  필요한 때:                                                ║
║  ① n을 여러 조각으로 분해 (소인수)                          ║
║  ② "바로 이전"이 아닌 "더 이전"을 참조 (우표)               ║
║  ③ 재귀가 2단계 이상 뒤를 참조 (피보나치)                   ║
║                                                           ║
╚═══════════════════════════════════════════════════════════╝
```

---

## 다음 편(8-D) 예고

**제8-D편**에서는 교재 5.3절의 내용을 다룬다:
- **재귀적 정의**(recursive definitions) — 수열, 집합, 함수의 재귀적 정의
- **구조적 귀납법**(structural induction) — 리스트, 트리 등의 귀납법
- Lean4에서의 재귀 함수 정의와 종료 증명
- `match`와 패턴 매칭의 고급 활용

---

**(끝)**
