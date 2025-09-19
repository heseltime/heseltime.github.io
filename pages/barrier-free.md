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

```python
from pathlib import Path
import fitz  # PyMuPDF
from datasets import Dataset
import orjson
import json
import re

# --- Parameters ---
# Directory in Drive containing pairs like:
#   foo_uncompressed.pdf                (source)
#   foo_bf_uncompressed.pdf             (gold, manually made accessible)
#   foo_a11y.json OR foo_a11y.txt       (optional report)
finetuning_dir = Path("/content/drive/MyDrive/finetuning")

# Keep inputs/outputs complete by default.
# Set to a VERY high limit or None to disable. Keeping None = no truncation.
max_lines = None    # e.g. set to 100000 if you need a cap

# If your reports are extremely long, you can cap them independently:
max_report_chars = None  # e.g. 100000; None = no cap

# Instruction prompt (domain-specific, terse, no CoT exposure)
instruction = """You are a low-level PDF accessibility fixer.

INPUTS:
1) PDF_CODE_RAW: Decompressed PDF page content streams (text operators, XObjects, structure refs).
2) ACCESSIBILITY_REPORT: Concrete issues to fix (missing /Alt, reading order, headings, structure tree, lang, etc.).

TASK:
Rewrite the PDF content streams to produce an accessible version. Fix issues per the report and PDF/UA best practices.

RESPONSE FORMAT:
Return ONLY the improved PDF content streams. No commentary, no markdown, no extra text.
"""

# --- Helper to extract /Contents stream from each page ---
def extract_content_streams(pdf_path: Path) -> str:
    doc = fitz.open(str(pdf_path))
    contents = []
    for page in doc:
        contents_obj = page.get_contents()
        if isinstance(contents_obj, list):
            for xref in contents_obj:
                stream = doc.xref_stream(xref)
                if stream:
                    contents.append(stream.decode(errors="ignore"))
        elif contents_obj:
            stream = doc.xref_stream(contents_obj)
            if stream:
                contents.append(stream.decode(errors="ignore"))
    doc.close()
    return "\n".join(contents)

def read_accessibility_report(base: str, folder: Path) -> str:
    """
    Looks for {base}_a11y.json or {base}_a11y.txt
    Returns raw text. If JSON, pretty-prints compactly.
    """
    json_path = folder / f"{base}_a11y.json"
    txt_path  = folder / f"{base}_a11y.txt"
    if json_path.exists():
        try:
            with open(json_path, "rb") as f:
                data = orjson.loads(f.read())
            # Compact but readable JSON as text
            return orjson.dumps(data, option=orjson.OPT_INDENT_2).decode("utf-8")
        except Exception as e:
            print(f"Warning: Failed to parse JSON report for {base}: {e}")
    if txt_path.exists():
        try:
            return txt_path.read_text(encoding="utf-8", errors="ignore")
        except Exception as e:
            print(f"Warning: Failed to read TXT report for {base}: {e}")
    return ""  # OK if missing
```

The following is good for checking everything is loading correctly:

```python
# --- Create instruction-style dataset (complete documents) ---
examples = []

bf_files = sorted(finetuning_dir.glob("*_bf_uncompressed.pdf"))
print(f"Found {len(bf_files)} gold (accessible) PDFs.")

for bf_path in bf_files:
    base = bf_path.name.replace("_bf_uncompressed.pdf", "")
    src_path = finetuning_dir / f"{base}_uncompressed.pdf"

    try:
        if not src_path.exists():
            print(f"Warning: Missing source for {bf_path.name}, skipping.")
            continue

        # Extract full streams
        src_code = extract_content_streams(src_path)
        tgt_code = extract_content_streams(bf_path)
        report   = read_accessibility_report(base, finetuning_dir)

        # Optional caps (disabled by default)
        if max_lines is not None:
            src_code = "\n".join(src_code.splitlines()[:max_lines])
            tgt_code = "\n".join(tgt_code.splitlines()[:max_lines])
        if max_report_chars is not None and report:
            report = report[:max_report_chars]

        # Previews for logging
        input_preview  = (src_code[:200] if src_code else "").replace("\n", "\\n")
        output_preview = (tgt_code[:200] if tgt_code else "").replace("\n", "\\n")
        report_preview = (report[:200] if report else "").replace("\n", "\\n")

        print(
            f"Adding example {base}:\n"
            "--- Input (first 200 chars) ---\n"
            f"{input_preview}\n"
            "--- Report (first 200 chars) ---\n"
            f"{report_preview}\n"
            "--- Output (first 200 chars) ---\n"
            f"{output_preview}\n"
        )

        # Single, complete example
        examples.append({
            "instruction": instruction,
            # We keep raw + report as a single "input" block to preserve completeness.
            "input": f"PDF_CODE_RAW:\n{src_code}\n\nACCESSIBILITY_REPORT:\n{report}",
            "output": tgt_code
        })

    except FileNotFoundError:
        print(f"Error: File not found: {src_path}. Skipping.")
    except Exception as e:
        print(f"Error processing pair {bf_path.name}: {e}")

print(f"Prepared {len(examples)} examples.")
```

Pouring it into the Alpaca format (Unsloth):

```python
# --- HuggingFace Dataset + Unsloth Prompt Formatting (Alpaca-style) ---
from datasets import Dataset

alpaca_prompt = """Below is an instruction that describes a task, paired with an input that provides further context. Write a response that appropriately completes the request.

### Instruction:
{}

### Input:
{}

### Response:
{}"""

EOS_TOKEN = tokenizer.eos_token

def formatting_prompts_func(batch):
    texts = []
    for i, inp, out in zip(batch["instruction"], batch["input"], batch["output"]):
        # Keep documents COMPLETE; no extra wrappers.
        texts.append(alpaca_prompt.format(i, inp, out) + EOS_TOKEN)
    return {"text": texts}

dataset = Dataset.from_list(examples)
dataset = dataset.map(formatting_prompts_func, batched=True, remove_columns=list(dataset.features.keys()))
print(dataset[:1]["text"][0][:1000])
```

Training procedure:

```python
# Training
from trl import SFTConfig, SFTTrainer

trainer = SFTTrainer(
    model = model,
    tokenizer = tokenizer,
    train_dataset = dataset,       # If you have a separate val set, pass eval_dataset=...
    dataset_text_field = "text",
    max_seq_length = max_seq_length,
    dataset_num_proc = 2,
    packing = False,               # Keep each document intact (no packing)
    args = SFTConfig(
        per_device_train_batch_size = 2,   # A100 can usually do 2–4 with 4-bit
        gradient_accumulation_steps = 4,   # effective batch size 8
        warmup_steps = 50,
        # num_train_epochs = 3,            # or use steps:
        max_steps = 1000,                  # adjust to your dataset size
        learning_rate = 2e-4,
        logging_steps = 5,
        optim = "adamw_8bit",
        weight_decay = 0.01,
        lr_scheduler_type = "cosine",
        seed = 3407,
        output_dir = "outputs",
        report_to = "none",
        bf16 = True,                       # good on A100
        gradient_checkpointing = True,
        save_steps = 200,
        save_total_limit = 2,
    ),
)
```

Notes on the **Alpaca** format:
- Comes from the Stanford **Alpaca dataset** (2023).
- Each example has three fields: `instruction`, `input`, and `output`.
- They are combined into a fixed template, which helps the model learn **instruction-following**

**Unsloth** is a fine-tuning library optimized for LLMs (LoRA/QLoRA training):
- It doesn’t change the format — it just trains more efficiently.

Notes on the trainer itself:
- **dataset_text_field = "text"**
  - Trainer reads Alpaca-style strings from the `text` column.

- **packing = False**
  - Each row is treated as a full sequence.
  - Easier to debug, but less GPU-efficient (padding overhead).

- **max_seq_length = max_seq_length**
  - Longer samples truncated, shorter ones padded.
  - Must be ≤ model’s context window.

- **per_device_train_batch_size = 2**
  - Small per-GPU batch.

- **gradient_accumulation_steps = 4**
  - Effective batch size = 2 × 4 = 8 (per device).

- **warmup_steps = 50**
  - Linear warmup before LR schedule kicks in.

- **max_steps = 1000**
  - Train for a fixed number of steps.
  - Alternative: use `num_train_epochs`.

- **learning_rate = 2e-4**
  - Standard for LoRA/QLoRA.
  - Too high for full fine-tune.

- **optim = "adamw_8bit"**
  - 8-bit AdamW via bitsandbytes.
  - Saves memory with minimal overhead.

- **weight_decay = 0.01**
  - Regularization on weights.

- **lr_scheduler_type = "cosine"**
  - Smooth decay after warmup.
  - Good default for SFT.

- **bf16 = True**
  - Efficient on A100/H100 GPUs.
  - Use `fp16=True` if bf16 unsupported.

- **gradient_checkpointing = True**
  - Saves memory, extra compute cost.

- **logging_steps = 5**
  - Logs loss/metrics frequently.

- **report_to = "none"**
  - No external logging.
  - Switch to `"wandb"` / `"tensorboard"` if desired.

- **save_steps = 200**
  - Save checkpoints every 200 steps.

- **save_total_limit = 2**
  - Keep only the 2 most recent checkpoints.

- **dataset_num_proc = 2**
  - Two CPU workers for dataset preprocessing.

- **output_dir = "outputs"**
  - Checkpoints and logs saved here.

- **seed = 3407**
  - Reproducibility.

Memory check:

```python
# @title Show current memory stats
gpu_stats = torch.cuda.get_device_properties(0)
start_gpu_memory = round(torch.cuda.max_memory_reserved() / 1024 / 1024 / 1024, 3)
max_memory = round(gpu_stats.total_memory / 1024 / 1024 / 1024, 3)
print(f"GPU = {gpu_stats.name}. Max memory = {max_memory} GB.")
print(f"{start_gpu_memory} GB of memory reserved.")
```

Actual training loop:

```python
# Train
trainer_stats = trainer.train()
```

My learning rate graph (training set of about 100 document pairs and their respective accessibility reports, based on Adobe PDF Services) follows.




## Comparison with training without meta-informational enrichment

The same training procedure was run on the same training documents, but without reports: at training time, we get the following training performance. (Different context sizes were tested, the model was `Llama3.1 (8B)`.)

[![Fine-tuning curve](/assets/img/barrier-free/barrier-free-fine-tuning_llama3.1-8B_alpaca_loss-curves-based-on-context-windows.png)](https://colab.research.google.com/drive/10g223UfFaE-kQ3bwvZeWhybuK8Rsz2Ma?usp=sharing)

[Google Colab notebook](https://colab.research.google.com/drive/10g223UfFaE-kQ3bwvZeWhybuK8Rsz2Ma?usp=sharing).


We will consider testing, for both scenarios, in the next section.


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

# Testing Set

# OOD? Uncertainty in LLM Inference

# More Testing Sets and Other Steps for this LLM Challenge 

<nav class="nav">
    <ul class="nav__list">
        <a href="/" class="nav__link">
            <i class="ri-home-5-line"></i>
            <span class="nav__name">
                Home
            </span>
        </a>

        <a href="/notes" class="nav__link">
            <i class="ri-swap-line"></i>
            <span class="nav__name">
                Feed
            </span>
        </a>

        <a href="/portfolio" class="nav__link">
            <i class="ri-slideshow-2-line"></i>
            <span class="nav__name">
                Portfolio
            </span>
        </a>

        <a href="/rDai" class="nav__link active-link">
            <i class="ri-robot-line"></i>
            <span class="nav__name">
                AI
            </span>
        </a>

        <a href="/rDse" class="nav__link">
            <i class="ri-command-line"></i>
            <span class="nav__name">
                Software
            </span>
        </a>

        <svg class="indicator" width="94" height="56" xmlns="http://www.w3.org/2000/svg">
            <ellipse cx="47" cy="28" rx="24" ry="28"/>
            <path d="M24 20C24 20 28 55.9999 48 56L0 55.9997C18 55.9998 24 20 24 20Z"/>
            <path d="M70 20C70 20 66 55.9999 46 56L94 55.9997C76 55.9998 70 20 70 20Z"/>
        </svg>
    </ul>

    <script src="{{ site.baseurl }}/assets-liquid-nav/js/main.js"></script>
</nav>