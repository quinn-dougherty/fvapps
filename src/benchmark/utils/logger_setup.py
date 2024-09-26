import logging
import sys
from datetime import datetime
from pathlib import Path

timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
script_name = Path(sys.argv[0]).stem
log_filename = Path("artefacts") / f"{script_name}_{timestamp}.log"

# Configure logging to write to the timestamped file
logging.basicConfig(
    filename=log_filename,
    filemode="w",
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.DEBUG,
)
