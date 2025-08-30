import os
import time
import google.generativeai as genai
from pathlib import Path

# --- 설정 (Configuration) ---
# 1. API 키 설정 (환경 변수에서 가져오기)
api_key = os.getenv("GEMINI_API_KEY")
if not api_key:
    raise ValueError("터미널에서 GEMINI_API_KEY 환경 변수를 설정해주세요.")
genai.configure(api_key=api_key)

# 2. 리팩토링할 소스 코드 경로 설정
source_directory = Path("./source") # <-- 이 폴더 이름이 정확한지 다시 한번 확인해주세요.

# 3. 리팩토링 프롬프트
refactoring_prompt = """You are an expert C programmer specializing in improving legacy code for SonarCloud analysis. Refactor the following C code to improve its Maintainability and Reliability. Focus on simplifying complex logic, removing code smells, and ensuring proper error handling, without altering its external functionality. Return ONLY the refactored C code, without any explanation, comments, or markdown formatting like ```c. Just the raw code."""

# --- 진단 코드 (Diagnostics) ---
print("--- 스크립트 진단을 시작합니다 ---")
print(f"1. 현재 스크립트 실행 위치 (CWD): {Path.cwd()}")
print(f"2. 소스 코드 검색 대상 폴더: {source_directory.resolve()}")

if not source_directory.is_dir():
    print(f"!!! 치명적 오류: '{source_directory}' 폴더를 찾을 수 없습니다. 폴더 이름이 정확한가요?")
    exit()

# --- 실행 (Execution) ---
model = genai.GenerativeModel('gemini-1.5-pro-latest')

# 대상 파일 찾기
files_to_refactor = list(source_directory.rglob("*.c")) + list(source_directory.rglob("*.h"))
total_files = len(files_to_refactor)

print(f"3. 찾은 소스 파일 개수: {total_files}개")

if total_files == 0:
    print("!!! 문제 발생: 소스 파일을 하나도 찾지 못했습니다. 대상 폴더 안에 .c 또는 .h 파일이 있는지 확인해주세요.")
    exit()

print("--- 리팩토링 작업을 시작합니다 ---")

for i, file_path in enumerate(files_to_refactor):
    try:
        print(f"[{i+1}/{total_files}] 처리 중: {file_path}")

        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            original_code = f.read()
        
        # 진단: 원본 코드의 일부를 출력
        print(f"  - 원본 코드 (앞 50자): {original_code[:50].replace('\n', ' ')}")

        # Gemini API 호출
        full_prompt = refactoring_prompt + "\n\n---\n\n" + original_code
        response = model.generate_content(full_prompt)
        
        # 진단: API 응답의 일부를 출력
        print(f"  - Gemini 응답 (앞 50자): {response.text[:50].replace('\n', ' ')}")

        # 결과물로 원본 파일 덮어쓰기
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(response.text)

        print("...파일 수정 완료. 다음 파일을 위해 1.2초 대기합니다.")
        time.sleep(15)

    except Exception as e:
        print(f"!!! 오류 발생: {file_path} 처리 중 문제 발생 - {e}")
        time.sleep(15)

print("--- 모든 작업이 완료되었습니다. `git status`를 확인해보세요. ---")
