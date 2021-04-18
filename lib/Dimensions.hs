 
module Dimension where


-- Homogénise l'ordre des quantités de bases dans les déclarations stp

----------------- Base quantities --------------------

-- Length -- 

dimension Length in Metre

-- Mass --

dimension Mass in Kilogramme

-- Time --

dimension Time in Second

unit Minute derives from Second with cvMinute2Second = (*60)
unit Hour   derives from Second with cvHour2Second = (*3600)
unit Day    derives from Second with cvDay2Second = (*86400)

-- Electric Current --

dimension Current in Ampere

-- Thermodynamic Temperature --

dimension Temperature in Kelvin

unit Degree derives from Kelvin with cvDegree2Kelvin = (-273.15)

-- Amount of Substance --

dimension Amount in Mole

-- Luminous Intensity -- 

dimension LumIntensity in Candela


----------------------- Useful quantities ------------------------------

-- Frequence --

alias Frequence = Time^(-1)
alias Hertz     = Second^(-1)

-- Speed --

alias Speed = Length * Time^(-1)

-- Acceleration --

alias Acceleration = Length * Time^(-2)

-- Pressure --

alias Pressure = Mass * Length^(-1) * Time^(-2)
alias Pascal = Kilogramme * Metre^(-1) * Second^(-2)

unit HectoPascal derives from Pascal with cvHectoPascal2Pascal = (*100)
unit Bar derives from Pascal with cvBar2Pascal = (*10e5)
unit Atm derives from Pascal with cvAtm2Pascal = (*(1.01325*10e5))
unit MmHg derives from Pascal with cvMmHg2Pascal = (*133.3)
unit Psi derives from Pascal with cvPsi2Pascal = (6.89476 * 10e3)


--------- Mecanic -------------

-- Force ---

alias Force  = Mass * Length * Time^(-2)
alias Newton = Kilogramme * Metre * Second^(-2)

-- Energy --

alias Energy = Mass * Length^2 * Time^(-2)
alias Joule = Kilogramme * Metre^2 * Second^(-2)

unit WattHour derives from Joule with cvWattHour2Joule = (*3600)

--------- Electricity -----------

-- Power --

alias Power = Mass * Length^2 * Time^(-3)
alias Watt = Kilogramme * Metre^2 * Second^(-3)

-- Electrical Potential --

alias Potential = ( Mass * Length^2 ) / ( Current * Time^3)
alias Volt      = ( Kilogramme * Metre^2 ) / ( Ampere * Second^3)

unit EVolt derives from Volt with cvEVolt2Volt = (/1.6e-19)

-- Resistance --

alias Resistance = Mass * Length^2 * Time^(-3) * Current^(-2)
alias Ohm        = Kilogramme * Metre^2 * Second^(-3) * Ampere^(-2)

-- Electric Charge --

alias Charge    = Current * Time
alias Coulomb   = Ampere * Second

-- Capacitance --

alias Capacitance = Time^4 * Current^2 * Length^(-2) * Mass^(-1)
alias Farad = Second^4 * Ampere^2 * Metre^(-2) * Kilogramme^(-1)
 
-- Conductance --

alias Conductance = Mass^(-1) * Length^(-2) * Time^3 * Current^2
alias Siemens = Kilogramme * Metre^2 * Second^(-2) * Ampere^(-2)

-- Electric Inductance --

alias ElecInductance = Mass * Length^2 * Time^(-2) * Current^(-2)
alias Henry = Kilogramme * Metre^2 * Second^(-2) * Ampere^(-2)

-- Magnetic B-Field  --

alias MagneticBField = Mass * Time^(-2) * Current^(-2)
alias Tesla = Kilogramme * Second^(-2) * Ampere^(-2)

-- Magnetic flux --

alias MagneticFlux = Mass * Length^2 * Time^(-2) * Current^(-1)
alias Weber = Kilogramme * Metre^2 * Second^(-2) * Ampere^(-1)

----------

alias Becquerel = Time^(-1)
alias Gray = Metre^2 * Second^(-2)
alias Sievert = Metre^2 * Second^(-2)


----------------- Fundamental Constants ? ----------------

-- not sure for storage reason (is it too little?)

constantAvogadro = 6.02214179 * 10e23 < Mole^(-1) >
constantBoltzmann = 1.3806504 * 10e-23 < Joule * Kelvin^(-1) >
constantEpsilonO = 8.854187817 * 10e-12 < Farad * Meter^(-1) >
constantElectronMass = 9.10938215 * 10e-31 < Kilogramme >
constantProtonMass = 1.672621637 * 10e-27   < Kilogramme >
constantE = 1.602176487 * 10e-9 < Coulomb >
constantGravitation = 6.67428 * 10e-11 < Meter^3 * Kilogramme^(-1) * Second^(-2)
constantPlanck = 6.62606896 * 10e-34 < Joule * Second >
constantRydberg = 10973731.568 < Meter^(-1) >
constantC = 299792458 < Meter * Second^(-1) >
constantStefanBoltzmann = 5.670400 * 10e-8 < Warr * Meter^(-2) * Kelvin^(-4) >
constantGaz = 8.314472 < Joule * Mole^(-1) * Kelvin^(-1) >
