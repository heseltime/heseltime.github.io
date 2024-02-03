---
title: progress-reports LLM Workflow (Test)
feed: show
date: 03-02-2024
---
# Let's Try Something Out

Based on [my repo](https://github.com/heseltime/progress-reports/) with a more detailed [setup section](https://github.com/heseltime/progress-reports/tree/main?tab=readme-ov-file#heres-the-setup-wrench) in the README.

## Use Case

([As per the repo README](https://github.com/heseltime/progress-reports/?tab=readme-ov-file#paperclip-progress--x-reports-paperclip-with-the-openai-api-postbox).)

I have a collection of daily reports in a folder somewhere, let's say they all follow the filename format "yyyymmdd.txt", so we know what month they pertain to, and I want to generate an LLM progress report mostly in third person, the type may or may not be asked for consultancy work or any job, here with a slant towards software engineering.

I want to run a program that takes care of the content accurately but flexibly and in the style I like, even perform some simple summation (this type of math an LLM can currently certainly already do) of hours worked (included in the daily report), thus automating away the monthly task and also doing the simple by-handy tallying of (billable, typically) hours worked.

[More after the jump](/curl)