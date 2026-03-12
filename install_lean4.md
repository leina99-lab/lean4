# Lean 4 설치 가이드 — 초보자용 단계별 안내 (macOS 및 Windows)

작성 기준: 2026-03-11

> 이 문서는 **본문은 계속 보이되**, 막히는 사람만 **`클릭` 섹션을 펼쳐서 추가 설명을 읽는 구조**로 작성한 안내서이다. GitHub는 `<details>`를 이용한 접기/펼치기와 tasklist를 지원하며, VS Code는 Markdown Preview를 제공한다.[^1][^2][^3]
>
> 이 파일을 **그냥 위에서 아래로 읽어도 되며**, 막히는 부분이 있으면 해당 단계의 `클릭` 안내만 펼쳐 읽으면 된다.

---

## 0. 먼저 알아둘 점

1. 이 문서는 **컴퓨터가 익숙하지 않은 사람**을 기준으로 썼다.
2. Windows 설명은 **명령 프롬프트(cmd)** 기준으로 적었다. PowerShell을 따로 배울 필요는 없다. 다만 Lean 설치 스크립트를 실행할 때는 **제공된 한 줄을 그대로 붙여넣는 용도**로 PowerShell이 한 번 등장한다.
3. macOS 설명은 **Terminal(터미널)** 기준으로 적었다.
4. 가능한 한 **마우스로 하는 방법**을 먼저 적고, 꼭 필요한 부분만 터미널 명령을 사용했다.
5. Lean 4를 웹에서만 쓰는 것은 입문 단계에서는 가능하지만, **프로젝트 생성**, **Mathlib 사용**, **파일 저장**, **패키지 관리**까지 하려면 결국 데스크톱 환경이 필요하다.[^4][^5][^7]

---

## 1. 이 가이드를 읽는 방법

### 1.1 기본 사용법

- 먼저 **굵은 글씨와 번호만 읽고 그대로 진행**한다.
- 어려운 말이 나오면 바로 아래의 **`클릭:`** 부분을 펼친다.
- 완료한 항목은 앞의 `[ ]`를 `[x]`로 바꿔 표시한다.
- GitHub에서 이 문서를 열면 tasklist를 클릭해서 표시할 수 있다.[^2]
- VS Code에서 이 문서를 열면 **Markdown Preview**로 보기 좋게 읽을 수 있다.[^3]

<details>
<summary>클릭: VS Code에서 Markdown Preview 여는 법</summary>

### macOS
- `Shift + Command + V` 를 누르면 미리보기가 열린다.
- 또는 `Command + K`를 누른 뒤, 손을 떼고 `V`를 누르면 옆으로 미리보기가 열린다.[^3]

### Windows
- `Ctrl + Shift + V` 를 누르면 미리보기가 열린다.
- 또는 `Ctrl + K`를 누른 뒤, 손을 떼고 `V`를 누르면 옆으로 미리보기가 열린다.[^3]

</details>

### 1.2 막혔을 때 질문하는 가장 쉬운 방법

다음 셋 중 하나만 보내면 된다.

- `Windows 5단계 3번에서 멈췄다.`
- `cmd 창에 이런 글자가 나왔다: ...`
- 화면 사진 1장

즉, **단계 번호만 알려도 이어서 도와줄 수 있다.**

---

## 2. 아주 짧은 용어 사전

- **VS Code**: 코드를 쓰는 프로그램이다.
- **확장(Extension)**: VS Code에 기능을 추가하는 작은 부품이다.
- **Lean 4 확장**: VS Code가 Lean 코드를 이해하게 해 주는 공식 확장이다.[^4][^6]
- **터미널 / cmd**: 글자를 입력해서 컴퓨터에 지시하는 창이다.
- **폴더**: 파일을 담는 상자라고 생각하면 된다.
- **경로(path)**: 폴더의 주소이다.
- **`cd`**: 현재 위치를 다른 폴더로 옮기는 명령이다.
- **`lake`**: Lean 프로젝트를 만들고 빌드하는 도구이다.[^5][^7]
- **`elan`**: Lean 버전을 자동으로 관리하는 도구이다.[^5]

---

## 3. 설치 전체 흐름 한눈에 보기

### macOS 진행표

- [ ] 1단계. VS Code 설치
- [ ] 2단계. Lean 4 확장 설치
- [ ] 3단계. 터미널 열기와 `git` 확인
- [ ] 4단계. `elan` 설치
- [ ] 5단계. Lean이 실제로 동작하는지 확인
- [ ] 6단계. 첫 Lean 프로젝트 만들기
- [ ] 7단계. 첫 Mathlib 프로젝트 만들기(선택)

---

# 4. macOS 설치

## macOS 1단계. VS Code 설치

**목표:** VS Code 프로그램이 Mac에 설치되고, 아이콘을 눌렀을 때 실행되면 된다.[^8]

### 해야 할 일

1. 브라우저에서 Visual Studio Code 다운로드 페이지를 연다.
2. macOS용 설치 파일(`.dmg`)을 내려받는다.[^8]
3. 내려받은 `.dmg` 파일을 연다.
4. `Visual Studio Code.app`을 `Applications` 폴더로 끌어다 놓는다.[^8]
5. `Applications` 폴더에서 VS Code를 두 번 클릭해 실행한다.

### 완료되었는지 확인하는 법

- VS Code 창이 열리면 이 단계는 끝이다.

<details>
<summary>클릭: “.dmg를 연다”와 “Applications로 끌어다 놓는다”가 무슨 뜻인지 모르겠다면</summary>

- `.dmg`는 macOS 설치 파일이다.
- 다운로드가 끝나면 보통 브라우저의 다운로드 목록 또는 Finder의 `Downloads` 폴더에 보인다.
- 그 파일을 두 번 클릭하면 설치 창이 열린다.
- 설치 창 안에 `Visual Studio Code` 아이콘과 `Applications` 폴더 그림이 함께 보이면, **VS Code 아이콘을 마우스로 잡아서 Applications 폴더로 끌어다 놓으면 된다.**
- 그 다음부터는 Launchpad나 Applications 폴더에서 VS Code를 열 수 있다.

</details>

---

## macOS 2단계. Lean 4 확장 설치

**목표:** VS Code 안에 공식 `Lean 4` 확장이 설치되면 된다.[^4][^6]

### 해야 할 일

1. VS Code를 연다.
2. 왼쪽 세로 메뉴에서 **네모 4개 모양 아이콘(Extensions)** 을 누른다.
3. 검색창에 `lean4`를 입력한다.
4. 작성자가 **`leanprover`** 인 **`Lean 4`** 를 찾는다.
5. **Install** 버튼을 누른다.[^5][^6]

### 완료되었는지 확인하는 법

- 확장 옆에 `Installed`가 보이면 된다.
- 설치 직후 Welcome 페이지나 Setup Guide가 열리면 정상이다.[^4][^6]

<details>
<summary>클릭: Setup Guide가 자동으로 안 열리면</summary>

1. 새 빈 파일 하나를 연다.
2. 오른쪽 위의 `∀` 아이콘을 누른다.
3. `Documentation…` 을 누른다.
4. `Show Setup Guide` 를 누른다.[^4][^6]

</details>

---

## macOS 3단계. 터미널 열기와 `git` 확인

**목표:** 터미널을 열고 `git` 명령이 되는지 확인하면 된다.[^5]

### 해야 할 일

1. `Command + Space`를 누른다.
2. `Terminal` 이라고 입력한다.
3. `Enter`를 눌러 Terminal을 연다.
4. 아래 명령을 입력하고 `Enter`를 누른다.

```bash
git --version
```

### 완료되었는지 확인하는 법

- `git version ...` 같은 글자가 나오면 성공이다.
- 설치 안내가 뜨면, 안내에 따라 설치를 마친 뒤 같은 명령을 한 번 더 실행한다.[^5]

<details>
<summary>클릭: 터미널 창이 정상인지 모르겠다면</summary>

- 터미널 창은 사람마다 모양이 조금 다르다.
- 검은색, 흰색, 회색 등 배경색은 달라도 괜찮다.
- 글자가 보이고, 마지막에 커서가 깜빡이면 정상이다.
- 무언가를 잘못 눌러도 대부분 큰일이 나지 않는다. 이 가이드의 명령만 그대로 입력하면 된다.

</details>

---

## macOS 4단계. `elan` 설치

**목표:** Lean 버전 관리자 `elan`이 설치되면 된다.[^5]

### 해야 할 일

터미널에 아래 명령을 **한 줄 통째로 복사해서 붙여넣고** `Enter`를 누른다.

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

설치 도중 선택지가 나오면 **기본 설치 옵션 `1`** 을 선택한다.[^5]

그다음 아래 명령을 입력한다.

```bash
source $HOME/.elan/env
```

### 완료되었는지 확인하는 법

- 명령 실행이 끝나고 다시 입력할 수 있는 상태가 되면 된다.
- 이어서 아래 명령을 입력했을 때 버전 정보가 보이면 거의 정상이다.

```bash
lake --version
```

<details>
<summary>클릭: `source $HOME/.elan/env`가 무엇인지 모르겠다면</summary>

이 줄은 **방금 설치한 Lean 도구의 위치를 현재 터미널에 알려주는 역할**을 한다. 어렵게 이해할 필요는 없다. 그냥 **설치 다음에 한 번 더 넣는 줄**이라고 생각하면 충분하다.[^5]

</details>

<details>
<summary>클릭: `lake --version`에서 오류가 나면</summary>

먼저 아래 둘 중 하나를 실행한 뒤 다시 시도한다.[^5]

```bash
source ~/.profile
```

또는

```bash
source ~/.bash_profile
```

그 뒤 다시 입력한다.

```bash
lake --version
```

</details>

---

## macOS 5단계. Lean이 실제로 동작하는지 확인

**목표:** VS Code 안에서 `.lean` 파일이 열리고, `#eval 1+1`이 정상 동작하면 된다.[^5]

### 해야 할 일

1. VS Code로 돌아간다.
2. 새 파일을 하나 만든다.
3. 파일명을 `Test.lean`으로 저장한다.
4. 아래 코드를 입력한다.

```lean
#eval 1+1
```

### 완료되었는지 확인하는 법

- 처음에는 Lean 툴체인을 설치하느라 잠시 기다릴 수 있다.[^5]
- 설치가 끝난 뒤 오류가 없고, 결과가 보이면 정상이다.[^5]

<details>
<summary>클릭: “파일을 저장한다”가 익숙하지 않다면</summary>

1. 위쪽 메뉴에서 `File` 을 누른다.
2. `Save` 를 누른다.
3. 파일 이름 칸에 `Test.lean` 을 입력한다.
4. 저장 위치는 일단 `Documents` 폴더로 두어도 충분하다.
5. `Save` 를 누른다.

</details>

---

## macOS 6단계. 첫 Lean 프로젝트 만들기

**목표:** `MyLeanProject`라는 새 프로젝트 폴더가 생기고, 빌드가 되면 된다.[^5][^7]

### 해야 할 일

터미널에 아래 명령을 **한 줄씩** 넣고, 매 줄마다 `Enter`를 누른다.

```bash
cd ~/Documents
lake new MyLeanProject
cd MyLeanProject
lake build
```

그 다음 VS Code에서 프로젝트 폴더를 연다.

1. VS Code를 연다.
2. 위쪽 메뉴에서 `File` 을 누른다.
3. `Open Folder...` 를 누른다.
4. `Documents` 안의 `MyLeanProject` 폴더를 선택한다.
5. 신뢰 여부를 묻는 창이 나오면 `Trust authors` 를 누른다.[^5]

### 완료되었는지 확인하는 법

- `Documents` 안에 `MyLeanProject` 폴더가 생기면 된다.
- VS Code에서 그 폴더 안의 Lean 파일들이 열리면 된다.

<details>
<summary>클릭: `cd ~/Documents`가 무슨 뜻인지 모르겠다면</summary>

- `cd` 는 **폴더를 이동하라**는 뜻이다.
- `~/Documents` 는 **내 문서 폴더**를 뜻한다.
- 따라서 이 줄의 뜻은 **“문서 폴더로 이동해라”** 이다.
- 외울 필요는 없다. 그냥 프로젝트를 만들기 전에 **작업 장소로 이동하는 한 줄**이라고 생각하면 된다.

</details>

<details>
<summary>클릭: `lake new MyLeanProject`가 무슨 뜻인지 모르겠다면</summary>

- `lake new` 는 **새 Lean 프로젝트를 만든다**는 뜻이다.[^7]
- `MyLeanProject` 는 새 폴더 이름이다.
- 즉, 이 줄은 **`MyLeanProject`라는 이름의 Lean 프로젝트 폴더를 만든다**는 뜻이다.

</details>

---

## macOS 7단계. 첫 Mathlib 프로젝트 만들기 (선택)

**목표:** Mathlib가 포함된 프로젝트를 만들면 된다.[^5]

### 해야 할 일

```bash
cd ~/Documents
lake +leanprover-community/mathlib4:lean-toolchain new MyMathlibProject math
cd MyMathlibProject
lake build
```

그 다음 VS Code에서 `File > Open Folder...` 로 `MyMathlibProject` 폴더를 연다.

### 완료되었는지 확인하는 법

- `MyMathlibProject` 폴더가 생기면 된다.
- 처음에는 Mathlib를 내려받느라 시간이 걸릴 수 있다.[^5]

<details>
<summary>클릭: 지금은 Mathlib 프로젝트를 만들지 않아도 되는가?</summary>

그렇다. 처음에는 **일반 Lean 프로젝트만 만들어도 충분하다.**

- Lean 자체 문법 연습만 하려면 `MyLeanProject`만으로도 된다.
- 수학 라이브러리를 쓰려면 나중에 `MyMathlibProject`를 만들면 된다.

</details>

---
##  설치 전체 흐름 한눈에 보기
### Windows 진행표

- [ ] 1단계. VS Code 설치
- [ ] 2단계. Lean 4 확장 설치
- [ ] 3단계. `cmd` 열기와 `git`, `curl` 확인
- [ ] 4단계. `elan` 설치
- [ ] 5단계. Lean이 실제로 동작하는지 확인
- [ ] 6단계. 첫 Lean 프로젝트 만들기
- [ ] 7단계. 첫 Mathlib 프로젝트 만들기(선택)

---
# 5. Windows 설치

## Windows 1단계. VS Code 설치

**목표:** VS Code 프로그램이 Windows에 설치되고 실행되면 된다.[^9]

### 해야 할 일

1. 브라우저에서 Visual Studio Code 다운로드 페이지를 연다.
2. Windows용 설치 파일을 내려받는다.[^9]
3. 내려받은 설치 파일(`VSCodeUserSetup-...exe`)을 두 번 클릭한다.[^9]
4. 화면 안내에 따라 설치를 끝낸다.
5. 설치가 끝나면 VS Code를 실행한다.

### 완료되었는지 확인하는 법

- VS Code 창이 열리면 된다.

<details>
<summary>클릭: 설치 파일을 실행했는데 겁이 난다면</summary>

- VS Code는 매우 널리 쓰이는 개발 도구이다.
- 설치 화면에서 보통 `Next`, `I accept`, `Next`, `Install` 순서로 진행하면 된다.
- 관리자 권한을 묻는 창이 뜨면, 본인 컴퓨터라면 일반적으로 허용하고 진행한다.

</details>

---

## Windows 2단계. Lean 4 확장 설치

**목표:** VS Code 안에 공식 `Lean 4` 확장이 설치되면 된다.[^4][^6]

### 해야 할 일

1. VS Code를 연다.
2. 왼쪽 세로 메뉴에서 **네모 4개 모양 아이콘(Extensions)** 을 누른다.
3. 검색창에 `lean4`를 입력한다.
4. 작성자가 **`leanprover`** 인 **`Lean 4`** 를 찾는다.
5. **Install** 버튼을 누른다.[^5][^6]

### 완료되었는지 확인하는 법

- 확장 옆에 `Installed`가 보이면 된다.
- Setup Guide가 자동으로 열리면 정상이다.[^5][^6]

<details>
<summary>클릭: Setup Guide가 자동으로 안 열리면</summary>

1. 새 빈 파일 하나를 연다.
2. 오른쪽 위의 `∀` 아이콘을 누른다.
3. `Documentation…` 을 누른다.
4. `Show Setup Guide` 를 누른다.[^4][^6]

</details>

---

## Windows 3단계. `cmd` 열기와 `git`, `curl` 확인

**목표:** 명령 프롬프트(cmd)를 열고 `git`과 `curl`이 되는지 확인하면 된다.[^5]

### 해야 할 일

1. 키보드의 Windows 키를 누른다.
2. `cmd` 라고 입력한다.
3. `명령 프롬프트` 또는 `Command Prompt`를 클릭한다.
4. 아래 두 줄을 **한 줄씩** 입력하고, 매 줄마다 `Enter`를 누른다.

```bat
git --version
curl --version
```

### 완료되었는지 확인하는 법

- `git version ...` 이 보이면 `git`은 정상이다.
- `curl ...` 관련 버전 글자가 보이면 `curl`도 정상이다.[^5]

<details>
<summary>클릭: cmd 창이 정상인지 모르겠다면</summary>

- 보통 `C:\Users\사용자이름>` 같은 글자가 보인다.
- 마지막에 깜빡이는 커서가 있으면 정상이다.
- 이것은 **지금 내가 어느 폴더에 있는지 보여주는 줄**이다.
- 무서워할 필요는 없다. 지금은 이 가이드의 명령만 복사해 넣으면 된다.

</details>

<details>
<summary>클릭: `git --version` 또는 `curl --version`에서 오류가 나면</summary>

공식 Lean 문서는 이 경우 해당 프로그램을 설치한 뒤, **cmd 창을 닫고 다시 열라**고 안내한다.[^5]

- `git`이 없으면 Git을 설치한다.
- `curl`이 없으면 Windows가 오래되었을 수 있으므로 업데이트 상태를 점검한다. 그래도 안 되면 다시 질문하면 된다.

</details>

---

## Windows 4단계. `elan` 설치

**목표:** Lean 버전 관리자 `elan`이 설치되면 된다.[^5]

### 해야 할 일

cmd 창에 아래 세 줄을 **한 줄씩** 넣고, 매 줄마다 `Enter`를 누른다.

```bat
curl -O --location https://elan.lean-lang.org/elan-init.ps1
powershell -ExecutionPolicy Bypass -f elan-init.ps1
del elan-init.ps1
```

설치 도중 선택지가 나오면 **기본 설치 옵션 `1`** 을 선택한다.[^5]

그 다음 아래 줄을 입력한다.

```bat
exit
```

이제 cmd 창이 닫힌다. 그 뒤 **새 cmd 창을 다시 열어야 한다.**[^5]

### 완료되었는지 확인하는 법

새 cmd 창에서 아래 명령을 넣었을 때 버전이 보이면 된다.

```bat
lake --version
```

<details>
<summary>클릭: 여기서 왜 PowerShell이 나오는데, 꼭 알아야 하는가?</summary>

그럴 필요는 없다.

- `powershell -ExecutionPolicy Bypass -f elan-init.ps1` 는 **방금 내려받은 설치 스크립트를 실행하는 한 줄**이다.
- PowerShell을 따로 배우는 단계가 아니다.
- 그냥 **그대로 복사해서 실행하는 한 줄**이라고 생각하면 충분하다.[^5]

</details>

<details>
<summary>클릭: `exit`를 왜 치는가?</summary>

`elan` 설치가 끝난 뒤에는 **새로운 cmd 창을 열어야** `lake` 같은 새 명령이 제대로 인식되는 경우가 많다. 그래서 현재 창을 닫고 새로 시작하는 것이다.[^5]

</details>

---

## Windows 5단계. Lean이 실제로 동작하는지 확인

**목표:** VS Code 안에서 `.lean` 파일이 열리고, `#eval 1+1`이 정상 동작하면 된다.[^5]

### 해야 할 일

1. VS Code로 돌아간다.
2. 새 파일을 하나 만든다.
3. 파일명을 `Test.lean`으로 저장한다.
4. 아래 코드를 입력한다.

```lean
#eval 1+1
```

### 완료되었는지 확인하는 법

- 처음에는 Lean 툴체인을 설치하느라 잠시 기다릴 수 있다.[^5]
- 설치가 끝난 뒤 오류가 없고, 결과가 보이면 정상이다.[^5]

<details>
<summary>클릭: Lean 툴체인 설치 중인지 아닌지 모르겠다면</summary>

처음에는 몇 초에서 몇 분 정도 기다릴 수 있다. 인터넷 속도와 컴퓨터 상태에 따라 차이가 있다. 중요한 것은 **조금 기다린 뒤에 빨간 오류가 사라지고, Lean 관련 기능이 살아나는지**를 보는 것이다.[^5]

</details>

---

## Windows 6단계. 첫 Lean 프로젝트 만들기

**목표:** `MyLeanProject`라는 새 프로젝트 폴더가 생기고, 빌드가 되면 된다.[^5][^7]

### 해야 할 일

cmd 창에 아래 명령을 **한 줄씩** 넣고, 매 줄마다 `Enter`를 누른다.

```bat
cd %USERPROFILE%\Documents
lake new MyLeanProject
cd MyLeanProject
lake build
```

그 다음 VS Code에서 프로젝트 폴더를 연다.

1. VS Code를 연다.
2. 위쪽 메뉴에서 `File` 을 누른다.
3. `Open Folder...` 를 누른다.
4. `Documents` 안의 `MyLeanProject` 폴더를 선택한다.
5. 신뢰 여부를 묻는 창이 나오면 `Trust authors` 를 누른다.[^5]

### 완료되었는지 확인하는 법

- `Documents` 안에 `MyLeanProject` 폴더가 생기면 된다.
- VS Code에서 그 폴더 안의 Lean 파일들이 열리면 된다.

<details>
<summary>클릭: `cd %USERPROFILE%\Documents`가 무슨 뜻인지 모르겠다면</summary>

- `cd` 는 **폴더를 이동하라**는 뜻이다.
- `%USERPROFILE%` 는 **내 사용자 폴더**를 뜻한다.
- `%USERPROFILE%\Documents` 는 **내 문서 폴더**를 뜻한다.
- 즉, 이 줄은 **문서 폴더로 이동하라**는 뜻이다.

명령이 끝난 뒤 줄 앞부분이 대략 이런 식으로 바뀌면 정상이다.

```text
C:\Users\내이름\Documents>
```

</details>

<details>
<summary>클릭: `lake build`가 무슨 뜻인지 모르겠다면</summary>

`lake build` 는 **방금 만든 Lean 프로젝트를 실제로 조립해서 문제가 없는지 확인하는 단계**라고 생각하면 된다.[^5][^7]

</details>

---

## Windows 7단계. 첫 Mathlib 프로젝트 만들기 (선택)

**목표:** Mathlib가 포함된 프로젝트를 만들면 된다.[^5]

### 해야 할 일

```bat
cd %USERPROFILE%\Documents
lake +leanprover-community/mathlib4:lean-toolchain new MyMathlibProject math
cd MyMathlibProject
lake build
```

그 다음 VS Code에서 `File > Open Folder...` 로 `MyMathlibProject` 폴더를 연다.

### 완료되었는지 확인하는 법

- `MyMathlibProject` 폴더가 생기면 된다.
- 처음에는 Mathlib를 내려받느라 시간이 걸릴 수 있다.[^5]

<details>
<summary>클릭: 일반 Lean 프로젝트와 Mathlib 프로젝트의 차이</summary>

- **일반 Lean 프로젝트**: Lean 문법과 간단한 코드 연습에 적합하다.
- **Mathlib 프로젝트**: 이미 만들어진 수학 라이브러리를 사용할 수 있다.[^5]

처음에는 일반 프로젝트부터 시작하고, 필요할 때 Mathlib 프로젝트로 넘어가도 충분하다.

</details>

---

# 6. 자주 막히는 부분만 따로 모아 보기

## 6.1 “터미널이 무섭다”는 느낌이 들 때

그 반응은 매우 자연스럽다. 처음에는 누구나 글자만 있는 창이 어렵다. 그러나 지금 필요한 것은 **명령을 이해하는 것보다, 정해진 줄을 그대로 넣는 것**이다. 즉, 지금 단계에서 중요한 것은 다음 두 가지뿐이다.

1. **한 줄을 그대로 붙여넣는다.**
2. **Enter를 누른다.**

이 두 가지만 되면 설치는 대부분 진행된다.

## 6.2 “폴더 이동”이 어렵게 느껴질 때

폴더 이동은 **작업 장소를 바꾸는 것**일 뿐이다.

- macOS: `cd ~/Documents`
- Windows: `cd %USERPROFILE%\Documents`

이 두 줄은 외울 필요가 없다. 그냥 **문서 폴더로 가는 줄**로 기억하면 충분하다.

## 6.3 “PowerShell이 나오면 포기하고 싶다”는 느낌이 들 때

이 가이드에서는 PowerShell을 **배워야 할 대상으로 취급하지 않는다.** Windows에서 단 한 줄을 실행하는 데만 사용한다. 즉,

- PowerShell을 공부할 필요는 없다.
- 제공된 줄을 복사해 넣기만 하면 된다.
- 이후 다시 cmd로 돌아오면 된다.

## 6.4 “Lean Web로만 공부하면 안 되는가?”

초기 문법 학습이나 짧은 실험은 웹 환경으로도 가능하다. 그러나 **실제 프로젝트 생성**, **Mathlib 사용**, **파일 관리**, **패키지 관리**는 데스크톱 환경에서 하는 편이 훨씬 안정적이다.[^4][^5][^7]

---

# 7. 이미 설치가 끝난 뒤에 가장 많이 하는 일

## 7.1 기존 프로젝트 열기

### macOS

```bash
cd ~/Documents
git clone https://github.com/<repository owner>/<repository name>.git
cd <repository name>
lake exe cache get
lake build
```

그 다음 VS Code에서 `File > Open Folder...` 로 해당 폴더를 연다.[^5]

### Windows

```bat
cd %USERPROFILE%\Documents
git clone https://github.com/<repository owner>/<repository name>.git
cd <repository name>
lake exe cache get
lake build
```

그 다음 VS Code에서 `File > Open Folder...` 로 해당 폴더를 연다.[^5]

## 7.2 Mathlib 업데이트

### macOS

```bash
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
lake update
lake exe mk_all
lake build
```

### Windows

```bat
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
lake update
lake exe mk_all
lake build
```

이 절차는 공식 문서에 제시된 Mathlib 업데이트 방법이다.[^5]

---

# 8. `lake new`를 정말 쉬운 말로 설명하면

`lake new` 는 **Lean 프로젝트를 새로 만드는 명령**이다.[^7]

예를 들어,

```bash
lake new MyLeanProject
```

의 뜻은 다음과 같다.

- `lake new` : 새 프로젝트를 만든다.
- `MyLeanProject` : 새 프로젝트 폴더 이름이다.

즉, **`MyLeanProject`라는 새 Lean 프로젝트 상자를 하나 만든다**고 생각하면 된다.

Mathlib까지 포함하고 싶으면,

```bash
lake new MyMathlibProject math
```

처럼 `math` 템플릿을 사용할 수 있다.[^7]

---

# 9. 이 가이드의 최소 목표

처음에는 아래 세 가지만 되면 충분하다.

- [ ] VS Code 설치 완료
- [ ] Lean 4 확장 설치 완료
- [ ] `Test.lean`에서 `#eval 1+1` 성공

이 세 가지가 되면 이미 **Lean 4 데스크톱 환경의 핵심 설치는 끝난 것**이다. 그다음에야 `lake new`와 Mathlib로 넘어가면 된다.[^4][^5]

---

# 10. 참고 문헌 및 공식 자료

[^1]: GitHub Docs, *Organizing information with collapsed sections*. `<details>`와 `<summary>`를 사용한 접기/펼치기 설명. <https://docs.github.com/en/get-started/writing-on-github/working-with-advanced-formatting/organizing-information-with-collapsed-sections>
[^2]: GitHub Docs, *About tasklists*. Markdown tasklist 설명. <https://docs.github.com/en/get-started/writing-on-github/working-with-advanced-formatting/about-tasklists>
[^3]: Visual Studio Code Docs, *Markdown and Visual Studio Code* 및 *Tips and Tricks*. Markdown Preview 단축키와 미리보기 기능 설명. <https://code.visualstudio.com/docs/languages/markdown> / <https://code.visualstudio.com/docs/getstarted/tips-and-tricks>
[^4]: Lean Lang, *Install Lean*. 공식 권장 설치 경로와 Setup Guide 재호출 경로를 설명한다. <https://lean-lang.org/install/>
[^5]: Lean Lang, *Manual Installation*. macOS 및 Windows에서의 `elan`, `lake`, Mathlib, 프로젝트 생성 절차를 설명한다. <https://lean-lang.org/install/manual/>
[^6]: Visual Studio Marketplace, *Lean 4 (leanprover)*. VS Code용 공식 Lean 4 확장 설명과 Setup Guide 재호출 경로를 포함한다. <https://marketplace.visualstudio.com/items?itemName=leanprover.lean4>
[^7]: Lean Lang, *Lake*. `lake new`, `lake init`, 템플릿(`std`, `exe`, `lib`, `math`)을 설명한다. <https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/>
[^8]: Visual Studio Code Docs, *Visual Studio Code on macOS*. `.dmg` 설치와 Applications 폴더 배치 설명. <https://code.visualstudio.com/docs/setup/mac>
[^9]: Visual Studio Code Docs, *Visual Studio Code on Windows*. Windows 설치 프로그램 실행 절차 설명. <https://code.visualstudio.com/docs/setup/windows>
