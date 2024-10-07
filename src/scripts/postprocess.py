"""Bringing it to huggingface"""

from benchmark.postprocessing.jsonl import convert_to_jsonl


def main():
    convert_to_jsonl(base_dir="artefacts")
