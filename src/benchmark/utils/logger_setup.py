import logging
import sys
from datetime import datetime
from pathlib import Path


def is_running_in_notebook():
    """Check if the code is running in a Jupyter notebook."""
    try:
        return "ipykernel" in sys.modules
    except:
        return False


def setup_logging():
    """
    Configure logging system.
    - In notebooks: console logging only
    - In scripts: file logging only
    """
    logger = logging.getLogger()
    logger.setLevel(logging.DEBUG)

    # Clear any existing handlers
    logger.handlers.clear()

    # Common format for all handlers
    formatter = logging.Formatter(
        "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
    )

    if is_running_in_notebook():
        # Notebook case: console logging only
        console_handler = logging.StreamHandler()
        console_handler.setFormatter(formatter)
        logger.addHandler(console_handler)
        logger.debug("Running in Jupyter notebook - console logging enabled")
    else:
        # Script case: file logging only
        script_name = Path(sys.argv[0]).stem
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

        # Create artifacts directory if it doesn't exist
        log_dir = Path("artefacts")
        log_dir.mkdir(exist_ok=True)

        log_filename = log_dir / f"{script_name}_{timestamp}.log"

        file_handler = logging.FileHandler(log_filename, mode="w")
        file_handler.setFormatter(formatter)
        logger.addHandler(file_handler)

    return logger


logging = setup_logging()
