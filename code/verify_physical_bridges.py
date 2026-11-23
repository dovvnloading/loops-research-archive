#!/usr/bin/env python3
"""Validate both the route register and theorem-level contracts."""
import sys

import verify_physical_bridge_routes as routes
import verify_physical_bridge_contracts as contracts


if __name__ == "__main__":
    try:
        routes.main()
        contracts.main()
    except (ValueError, KeyError, OSError) as error:
        sys.exit(str(error))
