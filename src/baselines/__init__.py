from typing import Type
from pathlib import Path
from .types import BaselineAgent, AgentConfig
from .anthropic_agent import ClaudeAgent
from .openai_agent import OpenAIAgent
from .google_agent import GoogleAgent
from .huggingface_agent import HuggingFaceAgent
from .baselines_config import (
    gemini_cfg,
    llama_cfg,
    gpt4o_cfg,
    prover_rl_cfg,
    sonnet_cfg,
    testhf_cfg,
)


def get_agent_by_name(name: str) -> Type[BaselineAgent]:
    match name:
        case "sonnet":
            return ClaudeAgent
        case "gpt-4o":
            return OpenAIAgent
        case "gemini":
            return GoogleAgent
        case "prover-rl":
            return HuggingFaceAgent
        case "llama":
            return HuggingFaceAgent
        case "testhf":
            return HuggingFaceAgent
        case _:
            raise ValueError(f"Model argument {name} unknown")


def get_config_by_name(name: str) -> dict:
    match name:
        case "sonnet":
            return sonnet_cfg
        case "gpt-4o":
            return gpt4o_cfg
        case "gemini":
            return gemini_cfg
        case "prover-rl":
            return prover_rl_cfg
        case "llama":
            return llama_cfg
        case "testhf":
            return testhf_cfg
        case _:
            raise ValueError(f"Model argument {name} unknown")


def build_agent(
    name: str, input_context: tuple[str, str], output_path: Path, config: dict
) -> BaselineAgent:
    return get_agent_by_name(name)(
        input_context=input_context,
        output_path=output_path,
        config=AgentConfig(**(get_config_by_name(name) | config)),
    )
