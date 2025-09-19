---
layout: Post
permalink: /barrier-free
title: Barrier-free PDFs
feedformat: none
---

The following is a synthesis of the final logical steps in concluding my Master's thesis, on the ECM (Enterprise Content Management) topic of "Suitability of Large Language Models for Making PDF-Documents More Accessible and Barrier-free (in Enterprise Content Management)" - the thesis itself has a broader view, here the focus is on the LLM/ML-tooling used in evaluation of LLM output on the task itself, with a view to advancing in this area as LLMs become more powerful and capable, and/or fine-tuned LLMs including tuning on this task or adjacent ones are produced (or in combination, powerful, fine-tuned LLMs).

# Meta-informational Approach

We start from a fine-tuning regime; here is the code assembled for a Google Colab A100 setup.

```python
%%capture
import os
if "COLAB_" not in "".join(os.environ.keys()):
    !pip install unsloth
else:
    # Do this only in Colab notebooks! Otherwise use pip install unsloth
    !pip install --no-deps bitsandbytes accelerate xformers==0.0.29.post3 peft trl triton cut_cross_entropy unsloth_zoo
    !pip install sentencepiece protobuf "datasets>=3.4.1" huggingface_hub hf_transfer
    !pip install --no-deps unsloth

!pip install pymupdf orjson
```

```python
from unsloth import FastLanguageModel
import torch

max_seq_length = 4096   # A100 is fine with this. You can try 8192 if your model supports it.
dtype = None            # None for auto; on A100 this will pick bfloat16.
load_in_4bit = True     # QLoRA-style training; keeps VRAM low.

# 4bit pre-quantized models we can swap in quickly:
fourbit_models = [
    "unsloth/Meta-Llama-3.1-8B-bnb-4bit",
    "unsloth/Meta-Llama-3.1-8B-Instruct-bnb-4bit",
    "unsloth/mistral-7b-instruct-v0.3-bnb-4bit",
    "unsloth/gemma-2-9b-bnb-4bit",
]

# Use any compatible 8B/7B. (You can switch this later to a DeepSeek-distill variant if Unsloth supports it.)
model, tokenizer = FastLanguageModel.from_pretrained(
    model_name = "unsloth/Meta-Llama-3.1-8B",  # try the -Instruct-bnb-4bit variant too
    max_seq_length = max_seq_length,
    dtype = dtype,
    load_in_4bit = load_in_4bit,
    # token = "hf_...",  # if you use gated models
)

model = FastLanguageModel.get_peft_model(
    model,
    r = 16,  # try 32 or 64 on A100 if you want more capacity
    target_modules = ["q_proj", "k_proj", "v_proj", "o_proj",
                      "gate_proj", "up_proj", "down_proj"],
    lora_alpha = 16,
    lora_dropout = 0,                # =0 is optimized in Unsloth
    bias = "none",
    use_gradient_checkpointing = "unsloth",  # great for long context
    random_state = 3407,
    use_rslora = False,
    loftq_config = None,
)
```

We work from a drive where we have a `finetuning` folder with training documents. The setting is like this, per document:

- non barrier-free version
- the manually edited, barrier-free version tagged ` bf` (with a preceeding space) before the file ending
- an accessibility report ending in `_a11y.json` (preceeding underscore) - more on this below

These details are included in case you want to recreate the setup, re-use this code, and contribute to the project of advancing in this area of LLM applications.

```python
from google.colab import drive
drive.mount('/content/drive')
```

## Accessibility Reports

Code, building on Adobe PDF Services (requiring this service's API credentials, id and key), also made for Google Colab and compatible with the directory setup described:

```python
%%capture
# Install Adobe PDF Services SDK 4.x (Python >= 3.10 on Colab)
!pip -q install --upgrade pip
!pip -q install "pdfservices-sdk==4.2.0"
```

```python
# (Re)confirm credentials are present (masked print for sanity)
import os, getpass

cid = os.getenv("PDF_SERVICES_CLIENT_ID")
csec = os.getenv("PDF_SERVICES_CLIENT_SECRET")

if not cid:
    cid = input("Enter PDF_SERVICES_CLIENT_ID: ").strip()
    os.environ["PDF_SERVICES_CLIENT_ID"] = cid

if not csec:
    csec = getpass.getpass("Enter PDF_SERVICES_CLIENT_SECRET (hidden): ").strip()
    os.environ["PDF_SERVICES_CLIENT_SECRET"] = csec

print("PDF_SERVICES_CLIENT_ID:", (cid[:4] + "…" + cid[-4:]) if cid and len(cid) >= 8 else "missing")
print("✅ Credentials set.")
```

Intended to run over a whole (Google Drive) directory, the same that is then used for training.

```python
# Force-remount Drive once (helps after FUSE errors)
from google.colab import drive
drive.mount('/content/drive', force_remount=True)
print("✅ Drive mounted.")
```

```python
# Core script (fixed credentials check + drive-safe writing + correct imports)
import os, re, json, time, logging, errno
from pathlib import Path
from typing import Optional, Tuple

from adobe.pdfservices.operation.auth.service_principal_credentials import ServicePrincipalCredentials
from adobe.pdfservices.operation.pdf_services import PDFServices
from adobe.pdfservices.operation.io.stream_asset import StreamAsset
from adobe.pdfservices.operation.io.cloud_asset import CloudAsset
from adobe.pdfservices.operation.pdf_services_media_type import PDFServicesMediaType
from adobe.pdfservices.operation.pdfjobs.jobs.pdf_accessibility_checker_job import PDFAccessibilityCheckerJob
from adobe.pdfservices.operation.pdfjobs.result.pdf_accessibility_checker_result import PDFAccessibilityCheckerResult
from adobe.pdfservices.operation.exception.exceptions import ServiceApiException, ServiceUsageException, SdkException

LOG = logging.getLogger("a11y-colab")
logging.basicConfig(level=logging.INFO, format="%(levelname)s: %(message)s")

# -------- Helpers --------

def get_pdf_services() -> PDFServices:
    client_id = os.environ.get("PDF_SERVICES_CLIENT_ID")
    client_secret = os.environ.get("PDF_SERVICES_CLIENT_SECRET")
    if not client_id or not client_secret:
        raise RuntimeError("Missing PDF_SERVICES_CLIENT_ID or PDF_SERVICES_CLIENT_SECRET.")
    creds = ServicePrincipalCredentials(client_id=client_id, client_secret=client_secret)
    return PDFServices(credentials=creds)

def safe_write_json_bytes(report_path: Path, json_bytes: bytes, attempts: int = 3) -> None:
    """Write JSON to Drive with retries. On Drive FUSE error, remount and retry, then fallback to /content."""
    for i in range(attempts):
        try:
            # Prefer pretty text if valid JSON
            try:
                data = json.loads(json_bytes.decode("utf-8"))
                report_path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
            except Exception:
                report_path.write_bytes(json_bytes)
            return
        except OSError as e:
            LOG.warning(f"Write attempt {i+1}/{attempts} failed for {report_path.name}: {e}")
            # If Drive FUSE flaked, try remount then retry
            from google.colab import drive as gc_drive
            try:
                gc_drive.mount('/content/drive', force_remount=True)
            except Exception:
                pass
            time.sleep(1.0)

    # Fallback to local if Drive keeps failing
    fallback_dir = Path("/content/a11y_reports_fallback")
    fallback_dir.mkdir(parents=True, exist_ok=True)
    fallback_path = fallback_dir / report_path.name
    try:
        data = json.loads(json_bytes.decode("utf-8"))
        fallback_path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    except Exception:
        fallback_path.write_bytes(json_bytes)
    LOG.error(f"Drive write failed repeatedly. Saved locally to: {fallback_path}")

# -------- File selection & naming --------

BF_PATTERNS = [
    r"[ _-]bf_uncompressed\.pdf$",
    r"[ _-]bf\.pdf$",
]
UNCOMPRESSED_PAT = r"_uncompressed\.pdf$"

def looks_accessible_variant(name: str) -> bool:
    low = name.lower()
    return any(re.search(p, low) for p in BF_PATTERNS)

def is_uncompressed_source(name: str) -> bool:
    return re.search(UNCOMPRESSED_PAT, name.lower()) is not None

def is_plain_pdf(name: str) -> bool:
    return name.lower().endswith(".pdf") and not is_uncompressed_source(name) and not looks_accessible_variant(name)

def base_for_report(pdf_path: Path) -> str:
    base = pdf_path.stem
    base = re.sub(r"[ _-]bf_uncompressed$", "", base, flags=re.IGNORECASE)
    base = re.sub(r"[ _-]bf$", "", base, flags=re.IGNORECASE)
    base = re.sub(r"_uncompressed$", "", base, flags=re.IGNORECASE)
    return base.strip()

def report_path_for(pdf_path: Path) -> Path:
    base = base_for_report(pdf_path)
    return pdf_path.with_name(f"{base}_a11y.json")

# -------- Adobe job runner with retry/backoff --------

def run_accessibility_check(pdf_bytes: bytes, retries: int = 3, backoff: float = 2.0) -> bytes:
    pdf_services = get_pdf_services()
    attempt = 0
    while True:
        try:
            input_asset = pdf_services.upload(input_stream=pdf_bytes, mime_type=PDFServicesMediaType.PDF)
            job = PDFAccessibilityCheckerJob(input_asset=input_asset)
            location = pdf_services.submit(job)
            resp = pdf_services.get_job_result(location, PDFAccessibilityCheckerResult)

            report_asset: CloudAsset = resp.get_result().get_report()
            stream_report: StreamAsset = pdf_services.get_content(report_asset)
            return stream_report.get_input_stream()  # raw bytes (JSON)

        except (ServiceApiException, ServiceUsageException, SdkException) as e:
            attempt += 1
            if attempt > retries:
                raise
            sleep_for = backoff * (2 ** (attempt - 1))
            LOG.warning(f"API error {type(e).__name__}: {e}. Retrying in {sleep_for:.1f}s...")
            time.sleep(sleep_for)

# -------- Directory traversal --------

def choose_sources(pdf_files: list[Path]) -> list[Path]:
    selected = []
    for p in pdf_files:
        name = p.name
        if looks_accessible_variant(name):
            continue
        if is_uncompressed_source(name) or is_plain_pdf(name):
            selected.append(p)
    return selected

def process_one(pdf_path: Path, overwrite: bool = False) -> Optional[Path]:
    report_path = report_path_for(pdf_path)
    if report_path.exists() and not overwrite:
        LOG.info(f"Skip (exists): {report_path.name}")
        return None

    LOG.info(f"Checking: {pdf_path.name}")
    pdf_bytes = pdf_path.read_bytes()
    json_bytes = run_accessibility_check(pdf_bytes)
    safe_write_json_bytes(report_path, json_bytes)
    LOG.info(f"Saved: {report_path.name}")
    return report_path

def process_dir(root: Path, overwrite: bool = False, only_paired: bool = True, recursive: bool = False) -> Tuple[int, int]:
    if recursive:
        pdfs = sorted([p for p in root.rglob("*.pdf") if p.is_file()])
    else:
        pdfs = sorted([p for p in root.iterdir() if p.suffix.lower() == ".pdf" and p.is_file()])

    if not pdfs:
        LOG.warning("No PDFs found.")
        return (0, 0)

    candidates = choose_sources(pdfs)

    if only_paired:
        bf_bases = set(base_for_report(p) for p in pdfs if looks_accessible_variant(p.name))
        candidates = [p for p in candidates if base_for_report(p) in bf_bases]

    made, skipped = 0, 0
    for src in candidates:
        try:
            out = process_one(src, overwrite=overwrite)
            if out is None:
                skipped += 1
            else:
                made += 1
        except Exception as e:
            LOG.error(f"Failed: {src.name} -> {e}")
    return (made, skipped)

print("✅ Batch generator (fixed) loaded.")
```

Execution

```python
# Run over your finetuning folder
from pathlib import Path

finetuning_dir = Path("/content/drive/MyDrive/finetuning")  # change if needed
OVERWRITE_EXISTING = False
ONLY_PAIRED = True
RECURSIVE = False

made, skipped = process_dir(finetuning_dir, overwrite=OVERWRITE_EXISTING, only_paired=ONLY_PAIRED, recursive=RECURSIVE)
print(f"Done. Created: {made}, Skipped: {skipped}")
```

# OOD? Uncertainty in LLM Inference

# More Tasks 