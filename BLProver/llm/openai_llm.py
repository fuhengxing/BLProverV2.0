"""
OpenAI API LLM接口实现
"""

import os
import json
import logging
import time
from datetime import datetime
from pathlib import Path
from typing import Optional, List, Dict, Tuple
from .base import LLMInterface
from ..utils.progress import emit_detail

logger = logging.getLogger(__name__)


def _print_llm_banner(title: str, detail: str = "") -> None:
    """打印精简版 LLM 日志横幅（不输出大段正文）。"""
    print("\n" + "=" * 80)
    print(title)
    if detail:
        print(detail)
    print("=" * 80)


def _append_empty_content_debug(
    model_name: str,
    finish_reason: Optional[str],
    reasoning_content: str,
    response,
) -> None:
    """
    当 content 为空时，将关键诊断信息落盘，便于排查上游模型是否仅返回 reasoning_content。
    """
    out_dir = Path("output") / "debug"
    out_dir.mkdir(parents=True, exist_ok=True)
    out_file = out_dir / "llm_empty_content.jsonl"

    usage_obj = getattr(response, "usage", None)
    if hasattr(usage_obj, "model_dump"):
        usage = usage_obj.model_dump()
    elif hasattr(usage_obj, "dict"):
        usage = usage_obj.dict()
    else:
        usage = usage_obj

    record = {
        "ts": datetime.now().isoformat(timespec="seconds"),
        "model": model_name,
        "finish_reason": finish_reason,
        "has_reasoning_content": bool(reasoning_content),
        "reasoning_content_preview": (reasoning_content or "")[:2000],
        "usage": usage,
    }
    with out_file.open("a", encoding="utf-8") as f:
        f.write(json.dumps(record, ensure_ascii=False) + "\n")

def _log_llm_response(content: str) -> None:
    """控制台打印模型回复正文。"""
    cap_s = os.getenv("LLM_LOG_RESPONSE_MAX_CHARS", "0").strip()
    cap = int(cap_s) if cap_s.isdigit() else 0
    text = content or ""
    truncated = False
    if cap > 0 and len(text) > cap:
        text = text[:cap]
        truncated = True
    body = "\n" + "=" * 80 + "\n" + "🤖 LLM RESPONSE\n" + "=" * 80
    if not text.strip():
        body += "\n(empty — message.content 为空或未返回)"
    else:
        body += "\n" + text
        if truncated:
            body += "\n... [truncated, LLM_LOG_RESPONSE_MAX_CHARS=%d]" % cap
    body += "\n" + "=" * 80 + "\n"
    emit_detail(body)


def _normalize_base_url(url: Optional[str]) -> Optional[str]:
    if not url:
        return url
    url = url.strip().rstrip("/")
    # OpenAI python SDK expects an OpenAI-compatible base URL; most providers use /v1
    if not url.endswith("/v1"):
        url = f"{url}/v1"
    return url


class OpenAILLM(LLMInterface):
    """OpenAI API大语言模型接口"""
    
    def __init__(
        self, 
        model_name: str = "deepseek-v4-pro",
        api_key: str = None,
        base_url: str = None,
        temperature: float = 0.7,
        max_tokens: int = 2048,
        thinking_mode: bool = False,
        reasoning_effort: str = "high",
    ):
        """
        初始化OpenAI客户端
        
        Args:
            model_name: 模型名称，默认为gpt-3.5-turbo
            api_key: API密钥
            base_url: API基础URL
            temperature: 生成温度
            max_tokens: 最大token数
            thinking_mode: 是否开启思考模式（DeepSeek V4 系列）
            reasoning_effort: 推理强度（high/max）
        """
        try:
            from openai import OpenAI
            
            # 使用提供的值或环境变量
            actual_api_key = (api_key or os.getenv("OPENAI_API_KEY") or "").strip()
            actual_base_url = _normalize_base_url(
                base_url
                or os.getenv("OPENAI_BASE_URL")
                or os.getenv("OPENAI_API_BASE")
            )

            if not actual_api_key:
                raise ValueError(
                    "缺少OPENAI_API_KEY。请通过参数api_key传入，或设置环境变量OPENAI_API_KEY。"
                )
            if not actual_base_url:
                # 如果不提供base_url，OpenAI SDK会使用其默认官方地址
                # 这里保持为None，避免写死任何第三方地址
                actual_base_url = None
            
            request_timeout = float(os.getenv("LLM_REQUEST_TIMEOUT", "600"))
            self.client = OpenAI(
                api_key=actual_api_key,
                base_url=actual_base_url,
                timeout=request_timeout,
            )
            self._request_timeout = request_timeout
            self.model_name = model_name
            self.temperature = temperature
            self.max_tokens = max_tokens
            self.thinking_mode = thinking_mode
            self.reasoning_effort = reasoning_effort
            logger.info(
                f"初始化OpenAI LLM: {model_name} at {actual_base_url or 'default'}"
            )
        except ImportError:
            raise ImportError("请安装openai库: pip install openai")
    
    def generate(self, prompt: str, system_prompt: str = "") -> str:
        """
        生成文本响应
        
        Args:
            prompt: 用户提示
            system_prompt: 系统提示
            
        Returns:
            str: 生成的文本
        """
        messages = []
        if system_prompt:
            messages.append({"role": "system", "content": system_prompt})
        messages.append({"role": "user", "content": prompt})
        
        try:
            # 控制台输出本次请求提示词（便于复现与调参）
            emit_detail(
                "\n" + "=" * 80
                + "\n" + "🤖 LLM REQUEST (system_prompt)" + "\n"
                + "=" * 80
                + "\n" + (system_prompt or "(empty)")
                + "\n" + "=" * 80
                + "\n" + "🤖 LLM REQUEST (user_prompt)" + "\n"
                + "=" * 80
                + "\n" + prompt
                + "\n" + "=" * 80 + "\n"
            )

            response = self._create_chat_completion(messages, max_tokens=self.max_tokens)
            content, finish_reason, has_reasoning, reasoning_content = self._extract_content_status(response)
            if content:
                _log_llm_response(content)
                return content

            # deepseek-reasoner 常见行为：先生成 reasoning_content；有时 finish_reason 也会是 stop，
            # 但 content 仍为空（服务端实现细节）。此时仍需要通过提高 max_tokens 重试来拿到最终 content。
            if has_reasoning:
                logger.warning(
                    "LLM 返回 reasoning_content 但 content 为空；finish_reason=%s",
                    finish_reason,
                )
                retried = self._retry_for_final_content(messages)
                if retried:
                    _log_llm_response(retried)
                    return retried

            logger.error(
                "LLM 返回空响应：message.content 为空"
            )
            _append_empty_content_debug(
                model_name=self.model_name,
                finish_reason=finish_reason,
                reasoning_content=reasoning_content,
                response=response,
            )
            _log_llm_response("")
            return ""
        except Exception as e:
            logger.error(f"OpenAI生成失败: {e}")
            raise
    
    def generate_with_messages(self, messages: List[Dict[str, str]]) -> str:
        """
        使用消息列表生成响应（OpenAI原生支持）
        
        Args:
            messages: 消息列表
            
        Returns:
            str: 生成的文本
        """
        try:
            # 控制台输出 messages（便于复现与调参）
            parts = ["\n" + "=" * 80, "🤖 LLM REQUEST (messages)", "=" * 80]
            for i, m in enumerate(messages):
                role = m.get("role", "unknown")
                content = m.get("content", "")
                parts.append("[%d] role=%s" % (i, role))
                parts.append(content)
                parts.append("-" * 80)
            parts.append("=" * 80 + "\n")
            emit_detail("\n".join(parts))

            response = self._create_chat_completion(messages, max_tokens=self.max_tokens)
            content, finish_reason, has_reasoning, reasoning_content = self._extract_content_status(response)
            if content:
                _log_llm_response(content)
                return content

            if has_reasoning:
                logger.warning(
                    "LLM 返回 reasoning_content 但 content 为空；finish_reason=%s",
                    finish_reason,
                )
                retried = self._retry_for_final_content(messages)
                if retried:
                    _log_llm_response(retried)
                    return retried

            logger.error(
                "LLM 返回空响应：message.content 为空"
            )
            _append_empty_content_debug(
                model_name=self.model_name,
                finish_reason=finish_reason,
                reasoning_content=reasoning_content,
                response=response,
            )
            _log_llm_response("")
            return ""
        except Exception as e:
            logger.error(f"OpenAI生成失败: {e}")
            raise

    def _create_chat_completion(self, messages: List[Dict[str, str]], max_tokens: int):
        kwargs = {
            "model": self.model_name,
            "messages": messages,
            "temperature": self.temperature,
            "max_tokens": max_tokens,
        }
        if self.model_name.startswith("deepseek-v4-"):
            kwargs["extra_body"] = {
                "thinking": {"type": "enabled" if self.thinking_mode else "disabled"}
            }
            if self.thinking_mode:
                kwargs["reasoning_effort"] = self.reasoning_effort
        max_retries = max(1, int(os.getenv("LLM_TIMEOUT_RETRIES", "3")))
        last_exc: Optional[Exception] = None
        for attempt in range(max_retries):
            try:
                return self.client.chat.completions.create(**kwargs)
            except Exception as exc:
                exc_name = type(exc).__name__
                is_timeout = "Timeout" in exc_name or "timeout" in str(exc).lower()
                if not is_timeout or attempt + 1 >= max_retries:
                    raise
                wait_s = min(30, 5 * (attempt + 1))
                logger.warning(
                    "LLM 请求超时 (attempt %d/%d, timeout=%ss)，%ds 后重试: %s",
                    attempt + 1,
                    max_retries,
                    self._request_timeout,
                    wait_s,
                    exc,
                )
                last_exc = exc
                time.sleep(wait_s)
        if last_exc:
            raise last_exc
        raise RuntimeError("LLM chat completion failed without exception")

    def _extract_content_status(self, response) -> Tuple[str, Optional[str], bool, str]:
        choice0 = response.choices[0]
        msg = choice0.message
        content = getattr(msg, "content", None) or ""
        finish_reason = getattr(choice0, "finish_reason", None)
        reasoning_content = getattr(msg, "reasoning_content", None) or ""
        has_reasoning = bool(reasoning_content)
        return content, finish_reason, has_reasoning, reasoning_content

    def _retry_for_final_content(self, messages: List[Dict[str, str]]) -> str:
        """
        不返回 reasoning_content 的前提下，尝试用更高 max_tokens 重试，争取拿到最终 content。
        上限由环境变量 LLM_MAX_TOKENS_CAP 控制（默认 8192）。
        """
        cap = int(os.getenv("LLM_MAX_TOKENS_CAP", "8192"))
        token_steps = [self.max_tokens, 4096, 8192]
        token_steps = [t for t in token_steps if t <= cap]
        # 去重并保持递增
        token_steps = sorted(set(token_steps))

        # 第一轮已经试过 self.max_tokens，从下一档开始
        for t in token_steps:
            if t <= self.max_tokens:
                continue
            logger.warning("检测到 content 为空且可能因 token 不足，重试 max_tokens=%s", t)
            resp = self._create_chat_completion(messages, max_tokens=t)
            content, finish_reason, has_reasoning, _ = self._extract_content_status(resp)
            if content:
                return content
            if not has_reasoning:
                # 没有 reasoning_content 还拿不到 content，继续重试意义不大
                break
        return ""

