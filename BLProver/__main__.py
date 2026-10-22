"""便于使用 ``python -m BLProver`` 直接启动 CLI（避免 runpy 警告）。"""

from .main import main

if __name__ == "__main__":
    main()
