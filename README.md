# Data sniffer on AXI4 Stream bus
This repository contains RTL and sim-only code for IP core that monitors data on the bus and tries
to detect IBAN number in the transmission frames.
# DISCLAIMER
This IP can only detect IBAN numbers from Switzerland and Poland, because IBAN numbers from different
countries follow different rules - so for simplicity only two sets of rules will be implemented.
For further information please check ISO standard number 13616 or [this](https://www.iban.com/structure)
website.
