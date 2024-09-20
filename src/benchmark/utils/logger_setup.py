import logging
from datetime import datetime
from pathlib import Path

timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
log_filename = Path("artefacts") / f"fvapps_{timestamp}.log"

# Configure logging to write to the timestamped file
logging.basicConfig(
    filename=log_filename,
    filemode="w",
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.DEBUG,
)
