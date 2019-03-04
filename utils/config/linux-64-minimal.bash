#!/bin/bash

CLB=`tput setaf 6`
CLR=`tput setaf 1`
CLNC=`tput sgr0`

confirm() {
    read -r -p "Proceed ? [y/N]" response
    case "$response" in
        [yY][eE][sS]|[yY])
            true
            ;;
        *)
            false
            ;;
    esac
}

if [ "$EUID" -ne 0 ]
then
    echo "${CLR}/!\\ Config script must be run as root /!\\${CLNC}"
    exit 1
fi

if [[ ! -z $(which opam) ]]
then
   echo -e "${CLR}/!\\ WARNING /!\\${CLNC}"
   echo -e "${CLR}/!\\ Opam was found on this system, this means that the following operation is /!\\${CLNC}"
   echo -e "${CLR}/!\\ DANGEROUS /!\\${CLNC}"
   confirm || exit 1
fi

echo -e "${CLB}Installing minimal system dependencies${CLNC}"
apt-get update -y
apt-get install cmake g++ doxygen pkg-config uuid-dev openjdk-11-jdk zlib1g-dev -y

echo -e "${CLB}Installing opam using system pm${CLNC}"
if [[ -z $(apt-search opam) ]]
then
    echo -e "${CLR}/!\\ Opam was not found in system repository /!\\${CLNC}"
    echo -e "${CLR}/!\\ Do yo want to add avsm/ppa to your system repositories? /!\\${CLNC}"
    confirm && add-apt-repository ppa:avsm/ppa
    apt-get update -y
fi
apt-get install opam m4 autoconf libgmp-dev -y

echo -e "${CLB}Updating opam config${CLNC}"
opam init -y
opam install alt-ergo why3 -y

echo -e "${CLB}Configuring Why3${CLNC}"
eval $(opam env)
why3 config

echo -e "${CLB}A reboot may be required${CLNC}"
confirm && reboot
