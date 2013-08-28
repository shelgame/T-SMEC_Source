	.title 1989 TurbonatorSMECv19
	.area ROM (ABS)
; SET TABS to 4 if text appears jumbled
;  ____________________________________________________________________________
; |									       \
; |									       |
; |   Mopar ECM SMEC							       |
; |   Based on 1989 Turbo I Codebase					       |
; |									       |
; | Code and original design and data Copyright 1988 by Chrysler Corporation   |                                    
; | This relocateable source is Copyright 2007 by Robert Lloyd		       |
; | Other code modules are Copyright 2013				       |
; |				  by Robert Lloyd			       |
; |									       |
; \____________________________________________________________________________|
;
; History
;
; Version 01
; 05/24/07 - Appears to compile corerctly !
;
; Version 02
; 05/24/07 - Change calibration data to match my cal (2.5 T1 ver6)
;            For reference, my car runs a stock (blueprinted) 2.5 T1, with
;            mitsu turbo 16psi boost, +20 injectors and a 3-bar MAP. This
;            should be a good base cal for just about any 2.5 T1 cars.
;
; Version 03
; 05/25/07 - Changed Baud Rate references to 3 constants; added option to
;            enable/disable serial interrupt routine (hi-speed logger); changed
;            the MAP transfer function values to a constant rather than hard-
;            coded.
;
; Version 04
; 06/29/07 - Fixed the staging mod switch reference.
;
; Version 05
; 06/29/07 - Modified the PumpEff calculation code to re-scale the table to
;            50-150%.
;
; Version 06
; 08/01/07 - Cleaned up stuff; added injector scaling info to table defs.
;
; Version 07
; 08/09/07 - Added anti-lag code.
;
; Version 08
; 08/13/07 - More cleanup; added ChEM2 calx definitions; changed fan control
;            speeds to be tuneable via constants rather than hard-coded.
; Version 09
; 09/12/07 - Added routine for 2-stage shift light control. Added constants 
;            and variables for shift light control.
; 
; Version 10
; 10/16/07 - Fixed the brclr/brset instructions that referenced the config 
;            constant.
;            * Starts and runs the car, finally. But, ASD will not turn off 
;            after key-on. Will not flash codes. CEL is always on also.
;            * Staging Limiter tested - OK
;            * Hi-Speed logger tested - OK
;
; Version 11 --- First Public Release ---
; 03/12/08 - Added assembler switches for ATX/MTX to simplify setup.
;            Added 2/3-Bar switches to assy source.
;            Source cal changed to MP 353 (for ATX) and 131 (for MTX).
;            Fixed Anti-Lag code (bad conditional branch instruction).
;            Fixed ldx (0x000e <-- 0x000d) in the 'zeroram from 3 to ff' routine.
;            Found and fixed an error in the Cruise Control Routine.
;            Found and fixed an assembler directive error in the switchable boost
;            polarity check code.
;            Fixed a code error (related to my original cal) in the Cruise routine
;            Fixed a couple of hard-coded MAP references to be configurable with 
;            MAP changes.
;            Added charge temp sensor enable to config flags
;            * ASD cycle is working correctly now
;            * CE light displays codes correctly
;
; Version 12
; 04/21/08 - Removed the Baro add in the Anti-Lag retard routine. BoostTarget is
;            actually a MAP target (baro is already added in) so, adding in Baro
;            was causing an overlow and incorreclty calculating the Anti-Lag.
;          - Fixed some .tbl file definitions that caused crashing problems with
;            D-Cal.
;          - Added in calibration values for 2.2l enigne (copied from T2 where 
;            applicable), and added in assembler switch to build 2.2 version. 
;
; Version 13
; 06/04/08 - There were a couple of constants from the MP MTX cal that caused 
;            the spark scatter to be inhibited in the MTX build. So, I changed 
;            these back to stock (same value as the ATX). It caused the idle to 
;            remain high during gear shifts. Probably added by Mopar to the MTX 
;            cal for road racing.
;          - Returned the 2.2l cal O2 ramps and adaptive cells back to stock
;            from the MP T2 (which tends to run rich due to the ramp
;            calibration).
;          - Added polarity switch for Staging Limiter.
;          - Added assembler option for WG control and a NEW T2-style WG control
;            routine. This routine is functioanlly similar to the T2 WG routine.
;            But, it's actually a modification of the T1 routine to invert the
;            duty cycle so that the T2 style WG plumbing can be used. The T1 WG
;            routine is tied into the knock retard system, so it would be 
;            impossible to simply paste the T2 WG control into Turbonator. The
;            T2 WG duty cycle tables are copied over from the T2 cal to be used 
;            as a baseline.
;          - Created a 3rd option for WG control. A custom routine based on the 
;            T1 code but with some modifications so that it can be used with a 
;            T2 style WG system (source control), but with a failsafe mode. 
;            Similar to the T3 WG control in that regard. Also added an 
;            additional lookup for this routine that increases the WG DC based 
;            on the delta to boost goal. This should help spoolup by maximizing
;            the DC during transient conditions.
;          - Changed the switchable boost implementation to a constant for lo-
;            boost instead of a table.
;          - Separated the Boost and WG Duty Cycle lookups to make it easier to
;            implement the T2 and Turbonator Custom WG control routines.
;          - Fixed a flag reference error in the speed calculation that caused
;            the speed to not update properly past 24mph.
;
; Version 14
; 08/07/08 - Found and fixed 2 fan control jumps.
;          - Found and fixed and error in the DRB memory location table.
;          - Found and fixed a DRB memroy table reference error.
;          - Found and fixed a DRB Switch test table reference error.
;          - Found and fixed a dis-assy error in the Spark Scatter Idle routine.
;            This was probably the cause of the rough/rich idle.
;
; Version 14.5
; 10/02/08 - Moved the flag location for the Turbonator Staging limiter due to
;            a previously undetected overlap with the cruise control routine.
;            This hopefully fixes the mystery mis-fire.
;          - Fixed the constant definition for the PIA output masks. This 
;            constant can be used to mask fault codes associated with the 
;            various PIA output bits.
;          - Deleted all of the boost control routines except the 'Turbonator'
;            boost control (modified, anti-lag version of the T1).
;
; Version 14.6
; 10/31/08 - Fixed a typo for the Staging Limiter/Misfire fix above.
;
; Version 14.7
; 11/13/08 - Fixed calibration values for P/T enrichment and spark scatter fuel.
;          - Added proper 2.2 calibration values for the same.
;
; Version 14.8
; 12/01/08 - Fixed calibration value for THRMAX for ATX (0x23 <-- 0x75).
;          - Made the anti-lag inclusion more robust. There was a possibility
;            it would be ignored.
;
; Version 14.9
; 01/06/09 - Fixed an arror in the AmbientTempSensor Fault detection routine that
;            probably caused a battery charging error I've had (but noone else
;            reported).
;          - Fixed a MAP scaling error with the RPMMAP table. This is not
;            actually a MAP-based table and should not have been scaled.
;
; Version 15
; 02/18/09 - Moved the calibration data to a template file for simplicity. All
;            calibration options will now be handled by changing the tempalte 
;            file instead of assembler options (.if statements). Though, MAP 
;            changes will still be handled by .if statements.
;          - Adated PTU Control routine from TBI/V6 SMEC using data tables from
;            '90/91 SBEC T1 cars (same as 'leftover' data in the '89 T1 code.
;            There is an overlap with the EMR control that must be disabled by 
;            flags.
;          - Removed the T1 and T2 boost control option (T2 never really worked
;            right). The only option now is Turbonator. You can get to the 
;            'stock' T1 boost control by setting the table
;            'DCWBST_FullThrottleWastegateDutyCycleAdjustment_FromBoostTarget' 
;            to return zero for all inputs.
;          - Added a 2nd option flags so that I can add a spark-based rev 
;            limiter. It's not working yet, but at least the code is 
;            structured for it.
;
; Version 15.1
; 02/27/09 - Fixed the Spark-based rev limiter code. Waiting to test.
;
; Version 15.2
; 03/30/09 - Corrected the jump for the staging limiter (to check for the 
;            option, was bypassed previously - I forgot to change it...)
;
; Version 15.3
; 09/02/09 - Corrected the template files for the aftermarket scantool codes. 
;            These were previously unknown codes (to me) and were commented out
;            of the assembly. I added them back in and included a de-coder. 
;            However, since this codebase is based on the '89 T1 (and the 
;            memory loations and DRB routines are as such), the codes need to 
;            stay unchanged.
;
; Version 16.0
; 09/22/09 - Removed all .if switches and added/corrected table definitions for
;            compatibility with MP Tune. The .if switches have been simply 
;            commented out. So, if you prefer to use CHeMAsm instead of 
;            MP Tuner, you will need to remove the comments.
;          - Added template definitions for S60, and Masi 8V ATX.
;          - Fixed several constant definitions, table definitions, and some 
;            cal data. Too numerous to detail each change...
;
; Version 16.1
; 01/27/10 - Removed the 150% PumpEff Rescale code and reverted it back to 
;            stock. This was apparently had a math error that caused an 
;            overflow that in turn caused the misfire problem.
;
; Version 16.2
; 02/01/10 - Fixed an error in the WG Control routine that was causing the 
;            wrong WGDC to be calculated. This was caused when I separated the 
;            boost lookup from the WGDC calculation.
;
; Version 16.3
; 02/16/10 - Updated all of the templates to improve the grouping and to take 
;            advantage of the new ramp editor in MP Tuner (table type 11).
;
; Version 16.4
; 06/02/10 - Updated the Anti-Lag code to keep it from activating when in 
;            vacuum.
;          - Updated the Charge Temp Sens Enable code to force a zero return 
;            for the fuel table.
;          - Updated the shift light code to be more simple, single setpoint 
;            style. Same code as T-LM.
;
; Version 16.5
; 07/28/10 - Fixed the PWADD table for the 2.2 templates. 
;            Added the dwell time from battery volts lookup from the Mexican 
;            SBEC cals. Should make for more consistent spark.
;
; Version 16.6
; 08/17/10 - Changed the Dwell calculation to be more like stock. The Mexican 
;            lookup did not work correctly in this code. Added a constant for 
;            minimum anti-dwell period (MINADW) to allow fine tuning.
;
; Version 16.7
; 08/24/10 - Added WOT battery volts target. Allows you to either dis-able (by
;            setting the targetlow) or step-up (by setting higher) the
;            alternator output when at WOT.
;          - Added MAPFLR to MAP scaling list. This may be a contributor to
;            engine stall when the CTS is unplugged.
;          - Reconfigured how the charge temp sesnor is enabled/disabled. This
;            likely is the cause of the engine stall when the CTS is unplugged.
;
; Version 16.8
; 10/17/10 - Fixed the bypass code for thecharge temp sensor (again). The way
;            I did it in 16.7 obviously wasn't right as it did not work
;            correctly.
;          - Removed the WOTBAT target since it seems to be causing a no-start
;            condition.
;
; Version 16.9
; 10/26/10 - Added PTU Routine to the main program loop so that it can run.
;          - Changed (again) the charge temp code to fix the stalling issue.
;
; Version 17.0
; 05/17/11 - Changed template format for MPT2.
;          - Removed the EMR Routine for space/execution time.
;          - Removed the CCD bus routine for space/execution time.
;
; Version 17.1
; 08/11/11 - Updated staging limiter to work when no switch is selected.
;          - Updated scaling for AESLOP (transient fuel).
;
; Version 17.2
; 12/17/11 - Testing spark cut rev limiter again...
;
; Version 18
; 04/30/12 - Completely re-written anti-lag and staging limiter.
;          - Anti-lag now goes to a single pre-set value rather than a
;            retard value.
;          - Anti-lag comes on at user-set RPM level.
;          - Staging limiter now has spark cut option. Spark cut is
;            rotating and has a selectable fraction.
;
; Version 18.1
; 06/05/12 - Added T2-type boost control.
; 06/26/12 - Fixed an error in the calling routine for the T2 Boost Control.
;          - Fixed the MAP scaling for the T2 boost-control tables
;          - Updated the T2 WGDC to match the T2 (or base cal) where appropriate.
;
; Version 18.2
; 01/01/13 - Fixed a table reference in the PTU code.
;          - Changed the PTU table naming to more accurately reflect the useage.
;          - Fixed a calculation in the Anit-lag code for negative values.
;
; Version 19
; 01/04/13 - Complete re-write of the launch control. Launch control is now a 
;            separate routine.
;          - Added Decel Fuel Cut code to completely turn off the injectors on 
;            decel.
;          - Updated the spark-cut rev limiter code to work better.
;          - Re-adopted 150% PEFTBL Scale. Working now.
;
; Verison 19.1
; 01/06/13 - Fixed code for the rotating spark cut counter.
;
; Version 19.2
; 01/07/13 - Fixed code for the decel fuel cut that prevented it from running.
;          - Fixed test code that was causing a misfire above 3776rpm
;          - Added code to force WOT fuelling while staging
;          - Added TPS Threshold for staging to prevent WOT fuelling at idle
;

version == 19

; ***********************************************************************

; Routines ending with "_MM" are called from MainProgramLoop.

; ***********************************************************************
; Code/data can be org'd anywhere in the $8000-$ffd5 range, except
; you MUST leave a hole from $b600-$b7ff (on chip eeprom). The interrupt
; vectors must be from $ffd6-$ffff.
; ***********************************************************************

DataOrg == 0x8000 ; do not change these values
CodeOrg == 0x9000
;IncludeFillerBytes = 1 ;to fill empty spaces with 0xff
;
; *****************************************************************************
; Calibration Template definition
; *****************************************************************************
;
; This template format will be used from T-SMEC v15 and later.
;
; I decided to switch to this format because it was getting clumsy
; trying to define the switches for all of the build options (MTX/ATX, 
; 2.2/2.5, boost control, etc.). This way, all the calibration data can be
; kept together in 1 place.
;
; T-SBEC will have it's own template format and the 2 CAN NOT be 
; interchanged. This is due to the different code structures between the
; SMEC and SBEC.
;
;
; Filename format:
;
;    T-SMEC_[displ]_[trans]_[ID]_[version].asm
;
; For example, the 1st tempalte file I made was from the 89 T1 Auto:
;
;    T-SMEC_25_ATX_a139_stock.asm
;
; This way you can start your T-SMEC build with any calibration.
;
; !!! This line is now written by MP Tuner when you specify the template to build with. !!!

.define CalDataFile /E:\Thumbdrive\BoostButton\Products\Cal Data\Customer Files\Norm Porter\2013_cal\T-SMEC_B151_normporter.tpl/

; ***********************************************************************
;
; Bit functions:
; Many bytes in the RAM contain status bits. For each of these the address value
; was separated into bit numbers, for example Flags_50 has b50_bit7 through b50_bit0.
; As the function of the bits was decoded, a global replace was performed to replace
; the bit name with a meaningful name, like:
;
;	b50_SparkEngineNotRunning   = $%10000000		;  -10000000-
;
; When working with bits, you can add several together using the "or" operator | like this:
;
;	b50_SparkEngineNotRunning | b50_BaroSolEnergized	;  -10100000-
;
; The inverse function ~ sets all bits except the ones specified, so:
;
;	~b50_SparkEngineNotRunning				;  -01111111-
;
; You can combine the inverse ~ with the or | like this:
;
;	~(b50_SparkEngineNotRunning | b50_BaroSolEnergized)	;  -01011111-
;
; The intent here was to make the logical functionality of the code easier to follow.
;
; ***********************************************************************
;
; Mopar ECM - 68HC11 Disassembly
; 1989 Turbo I
;
; Custom disassembler
; Copyright ï¿½ 2012 by Robert Lloyd.
; www.boostbutton.com

; generic bits:

bit_bit7			= $%10000000	;
bit_bit6			= $%01000000	;
bit_bit5			= $%00100000	;
bit_bit4			= $%00010000	;
bit_bit3			= $%00001000	;
bit_bit2			= $%00000100	;
bit_bit1			= $%00000010	;
bit_bit0			= $%00000001	;
bit_tophalf			= $%11110000	; top 4 bits
bit_bothalf			= $%00001111	; bottom 4 bits
bit_toptwo			= $%11000000	; top 2 bits
bit_bottwo			= $%00000011	; bottom 2 bits
bit_all 			= $%11111111	; all bits
bit_none			= $%00000000	; not bits

; RAM (bottom 256 bytes)

ACClutchToggleVar                                          == 0x009A;MPScan;ACTOG;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
AdaptiveCellUpdateTimer_IncrementedEveryDistRisingEdge     == 0x0089;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
AdaptiveRetardIndex                                        == 0x002B;MPScan;ARIDX;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
AFRatio                                                    == 0x00CE;MPScan;AFRATIO;byte;ratio;0.0;0.00;30.00;255.00;255.00;1.00;0.00;100.00;gauge-a
AmbientAirTempVolts                                        == 0x0071;MPScan;AMBVLT;byte;volts;0.0;0.00;5.00;1.00;1.00;1.00;0.00;5.00;gauge-a
AntiDwellTime_HB                                           == 0x008D;MPScan;ADWELL;word;mSec;0.00;0.00;65.00;5.00;1.00;1.00;0.00;65.00;graph
AntiDwellTime_LB                                           == 0x008E;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
ATMOffset                                                  == 0x00BB;MPScan;ATMOFS;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
AutoCalCell0                                               == 0x000F;MPScan;CELL0;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
AutoCalCell1                                               == 0x0010;MPScan;CELL1;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
AutoCalCell10                                              == 0x0019;MPScan;CELL10;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
AutoCalCell11                                              == 0x001A;MPScan;CELL11;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
AutoCalCell12idle                                          == 0x001B;MPScan;CELL12;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
    b0c_bit7			= $%10000000	;
    b0c_bit6			= $%01000000	;
    b0c_UseAIS		        = $%00100000	;Too much boost
    b0c_bit4			= $%00010000	;
    b0c_ATXInGear		= $%00001000	;Auto in gear
    b0c_ATXChngGear		= $%00000100	;Auto just changed gears
    b0c_bit1			= $%00000010	;
    b0c_bit0			= $%00000001	;
AutoCalCell2                                               == 0x0011;MPScan;CELL2;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
AutoCalCell3                                               == 0x0012;MPScan;CELL3;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
AutoCalCell4                                               == 0x0013;MPScan;CELL4;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
AutoCalCell5                                               == 0x0014;MPScan;CELL5;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
AutoCalCell6                                               == 0x0015;MPScan;CELL6;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
AutoCalCell7                                               == 0x0016;MPScan;CELL7;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
AutoCalCell8                                               == 0x0017;MPScan;CELL8;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
AutoCalCell9                                               == 0x0018;MPScan;CELL9;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
AverageMAPValue                                            == 0x0061;MPScan;AVGMAP;word;psi;0.0;0.00;30.00;5.00;1.00;1.00;0.00;29.40;gauge-a
AverageTPSVolts                                            == 0x0065;MPScan;AVGTPS;word;volts;0.0;0.00;5.00;1.00;1.00;1.00;0.00;5.00;gauge-a
b45_IPL1                                                   == 0x0045;MPScan;IPL1;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
b46_IPL2                                                   == 0x0046;MPScan;IPL2;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
BaroPressure                                               == 0x000E;MPScan;BARO;byte;psi;0.0;0.00;30.00;5.00;1.00;1.00;0.00;29.4;gauge-d
BaseFuelModifier                                           == 0x00D9;MPScan;FMOD;byte;%;0.0;0.00;100.00;255.00;255.00;1.00;0.00;100.00;gauge-a
BatteryVolts                                               == 0x006B;MPScan;BATVLT;byte;volts;0.0;0.00;16.00;4.00;1.00;1.00;0.00;16.00;gauge-a
BitFlags_1c                                                == 0x001C;MPScan;BF_1C;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
BitFlags_1d                                                == 0x001D;MPScan;BF_1D;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
BitFlags_27                                                == 0x0027;MPScan;FLAG27;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
    b1e_errLostFJ2		= $%10000000	; 44 Loss of FJ2
    b1e_errNothing		= $%01000000	; 45 Nothing (overboost)
    b1e_errHighVoltage		= $%00100000	; 46 Battery Volts High
    b1e_errLowVoltage		= $%00010000	; 47 Battery Volts Low
    b1e_errStuckLean		= $%00001000	; 51 Lean condition
    b1e_errStuckRich		= $%00000100	; 52 Rich Condition
    b1e_errChecksum		= $%00000010	; 53 Prom Checksum
    b1e_errDistSync		= $%00000001	; 54 Distributor Sync
BitFlags_2d                                                == 0x002D;MPScan;FLAG2D;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
    b1f_errAcCutoutRelay	= $%10000000	; 33 AC Cutout Relay
    b1f_errSpeedCtlSolenoid	= $%01000000	; 34 Speed Ctl Solenoid
    b1f_errRadFanRelay		= $%00100000	; 35 Radiator Fan Relay
    b1f_errWastegateSolenoid	= $%00010000	; 36 Wastegate Solenoid
    b1f_errBaroReadSolenoid	= $%00001000	; 37 Barometric Read Solenoid
    b1f_errChargingSystem	= $%00000100	; 41 Charging System
    b1f_errASDRelay		= $%00000010	; 42 Auto Shutdown Relay
    b1f_errIgnitionCoil 	= $%00000001	; 43 Ignition Coil Control
BitFlags_2e                                                == 0x002E;MPScan;FLAG2E;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
    b20_errCoolantTempSensor	= $%10000000	; 22 Coolant Temp Sensor
    b20_errChargeTempSensor	= $%01000000	; 23 Charge Temp Sensor
    b20_errTPS			= $%00100000	; 24 Throttle Position
    b20_errAIS			= $%00010000	; 25 AIS Motor
    b20_errInjectorCurrent	= $%00001000	; 26 Injector Current Limit Not Achieved
    b20_errInjectorDriver	= $%00000100	; 27 Injector Driver interface
    b20_errPurgeSolenoid	= $%00000010	; 31 Purge Solenoid
    b20_errEGR		        = $%00000001	; 32 Exh Gas Recirc Solenoid
BitFlags_47                                                == 0x0047;MPScan;FLAG47;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
    b21_errNotCranked		= $%10000000	; 11 Engine Not Cranked Since Battery Disconnected
    b21_errMemPowerLost 	= $%01000000	; 12 Memory Standby Power Lost
    b21_errMapPneumatic 	= $%00100000	; 13 MAP Pneumatic
    b21_errMapElectrical	= $%00010000	; 14 MAP Electrical
    b21_errDistanceSensor	= $%00001000	; 15 Vehicle Distance Sensor
    b21_errBattVoltageSense	= $%00000100	; 16 Battery Voltage Sense
    b21_errEngineTooCool	= $%00000010	; 17 Engine Running Too Cool (thermostat)
    b21_errO2Sensor		= $%00000001	; 21 Oxygen Sensor
BitFlags_4e                                                == 0x004E;MPScan;FLAG4E;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
    b22_bit7			= $%10000000	; 44 Loss of FJ2
    b22_bit6			= $%01000000	; 45 Overboost
    b22_bit5			= $%00100000	; 46 Battery Volts High
    b22_bit4			= $%00010000	; 47 Battery Volts Low
    b22_bit3			= $%00001000	; 51 Lean condition
    b22_bit2			= $%00000100	; 52 Rich Condition
    b22_bit1			= $%00000010	; 53 Prom Checksum
    b22_bit0			= $%00000001	; 54 Distributor Sync
BitFlags_4f                                                == 0x004F;MPScan;FLAG4F;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
    b23_bit7			= $%10000000	; 33 AC Cutout Relay
    b23_bit6			= $%01000000	; 34 Speed Ctl Solenoid
    b23_bit5			= $%00100000	; 35 Radiator Fan Relay
    b23_bit4			= $%00010000	; 36 Wastegate Solenoid
    b23_bit3			= $%00001000	; 37 Barometric Read Solenoid
    b23_bit2			= $%00000100	; 41 Charging System
    b23_bit1			= $%00000010	; 42 Auto Shutdown Relay
    b23_bit0			= $%00000001	; 43 Ignition Coil Control
BitFlags_50                                                == 0x0050;MPScan;FLAG50;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
    b24_bit7			= $%10000000	; 22 Coolant Temp Sensor
    b24_bit6			= $%01000000	; 23 Charge Temp Sensor
    b24_bit5			= $%00100000	; 24 Throttle Position
    b24_bit4			= $%00010000	; 25 AIS Motor
    b24_bit3			= $%00001000	; 26 Injector Current Limit Not Achieved
    b24_bit2			= $%00000100	; 27 Injector Driver interface
    b24_bit1			= $%00000010	; 31 Purge Solenoid
    b24_bit0			= $%00000001	; 32 Exh Gas Recirc Solenoid
BitFlags_51                                                == 0x0051;MPScan;FLAG51;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
    b25_bit7			= $%10000000	; 11 Engine Not Cranked Since Battery Disconnected
    b25_bit6			= $%01000000	; 12 Memory Standby Power Lost
    b25_bit5			= $%00100000	; 13 MAP Pneumatic
    b25_bit4			= $%00010000	; 14 MAP Electrical
    b25_bit3			= $%00001000	; 15 Vehicle Distance Sensor
    b25_bit2			= $%00000100	; 16 Battery Voltage Sense
    b25_bit1			= $%00000010	; 17 Engine Running Too Cool
    b25_bit0			= $%00000001	; 21 Oxygen Sensor
BitFlags_52                                                == 0x0052;MPScan;FLAG52;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
BitFlags_53                                                == 0x0053;MPScan;FLAG53;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
    b27_bit7			= $%10000000	; Cruise
    b27_bit6			= $%01000000	; Cruise
    b27_bit5			= $%00100000	; Cruise
    b27_bit4			= $%00010000	; Cruise
    b27_ParkNeutral		= $%00001000	; Park/Neutral, or always clear on manual
    b27_bit2			= $%00000100	; Something else with Park/Neutral
    b27_bit1          	        = $%00000010	; Cruise
    b27_bit0	                = $%00000001	; Cruise
BitFlags_54                                                == 0x0054;MPScan;FLAG54;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
BitFlags_55                                                == 0x0055;MPScan;FLAG55;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
BitFlags_56                                                == 0x0056;MPScan;FLAG56;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
BitFlags_AIS                                               == 0x000C;MPScan;FLAGAIS;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
BoostDelta_Signed                                          == 0x00CA;MPScan;DLTBST;byte;psi;0.0;-15;15;5;1;1.00;-15;14.4;gauge-a
    pia1abuf_CruiseVent 	= $%10000000	; Cruise Vent
    pia1abuf_CELight		= $%01000000	; Check Engine Light
    pia1abuf_ASDRelay		= $%00100000	; ASD Relay
    pia1abuf_FanRelay		= $%00010000	; Fan Relay
    pia1abuf_ACRelay		= $%00001000	; A/C Clutch Relay
    pia1abuf_PartThrotUnlock	= $%00000100	; Part Throttle Unlock
    pia1abuf_PurgeSolenoid	= $%00000010	; Purge Solenoid
    pia1abuf_CruiseVacuum	= $%00000001	; Cruise Vacuum
BoostTarget                                                == 0x00D8;MPScan;TGTBST;byte;psi;0.0;0.00;29.00;255.00;255.00;1.00;0.00;29.00;gauge-a
    b2d_EGR			= $%10000000	; EGR Active
    b2d_bit6			= $%01000000	;
    b2d_ReadBaroRequired	= $%00100000	; Read Baro At Next Opportunity
    b2d_EMR			= $%00010000	; Emission Maint Reminder
    b2d_bit3			= $%00001000	; Not used
    b2d_bit2			= $%00000100	; Not used
    b2d_ais1			= $%00000010	; AIS Step Phase - specifies which of the bit patterns
    b2d_ais0			= $%00000001	; AIS Step Phase   is being output to the stepper motor
    b2d_both			= $%00000011
CalculatedSparkAdvance                                     == 0x00A0;MPScan;SPKADV;byte;deg;0.0;0.00;127.00;255.00;255.00;1.00;0.00;127.00;gauge-d
    b2e_bit7        		= $%10000000	; Coolant temp filter/store?
    b2e_bit6			= $%01000000	; Coolant temp filter/store?
    b2e_AtIdle			= $%00100000	; Just returned to idle
    b2e_AcClutch		= $%00010000	; AC clutch engaged
    b2e_bit3			= $%00001000	; ?
    b2e_bit2			= $%00000100	; AC?
    b2e_bit1			= $%00000010	;
    b2e_bit0			= $%00000001	;
    b2e_BadO2Read		= $%00000011    ;Indicates a bad O2 sensor reading?

ChargeTemp                                                 == 0x005F;MPScan;IATMP;byte;volts;0.0;0.00;5.00;1.00;1.00;1.00;0.00;5.00;gauge-d
    b2f_bit7			= $%10000000	; Cruise not enabled
    b2f_bit6			= $%01000000	; Resuming
    b2f_bit5			= $%00100000	; Not used
    b2f_bit4			= $%00010000	; Cruise Engaged
    b2f_bit3			= $%00001000	; Cruise ?
    b2f_bit2			= $%00000100	; Cruise ?
    b2f_bit1			= $%00000010	; Cruise ?
    b2f_bit0			= $%00000001	; Cruise ?

ClearTheErrorTimer_0                                       == 0x0043;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
ClearTheErrorTimer_1                                       == 0x0044;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
CoolantTemp                                                == 0x006A;MPScan;COOLT;byte;degF;0;-20.00;260.00;10.00;1.00;1.00;-200.00;260.00;gauge-a
CountdownTimerFromKeyOn                                    == 0x0085;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Counter_AdaptiveMem_Erase                                  == 0x0087;MPScan;CNTAMER;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Counter_Cruise                                             == 0x0030;MPScan;CNTCRS;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Counter_EPP_MaxFF                                          == 0x0075;MPScan;CNTEPP;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Counter_FallingEdgeEPP_MaxFF                               == 0x0074;MPScan;CNTFE;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Counter_MainLoop                                           == 0x0080;MPScan;CNTMNL;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Counter_PartThrottleUnlock                                 == 0x00D4;MPScan;CNTPTU;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Counter_PrimaryAndSecondaryRamp                            == 0x007D;MPScan;CNTRMP;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Counter_PrimaryRamp                                        == 0x0093;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Counter_SomethingWithDistributor                           == 0x003F;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Counter_SparkCut                                           == 0x00D3;MPScan;CNTSPK;byte;;0;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-d
Counter_SpeedSensorInterrupt_HB                            == 0x00CB;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Counter_SpeedSensorInterrupt_LB                            == 0x00CC;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Counter_SpeedSensorInterrupt2_HB                           == 0x0029;MPScan;CNTSSI;word;;;0.00;65,535.00;255.00;255.00;1.00;0.00;65,535.00;gauge-a
Counter_SpeedSensorInterrupt2_LB                           == 0x002A;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Counter_TimerPastHalfwayBetweenDistPulses                  == 0x004C;MPScan;CNTHLFD;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Counter_TimerRegHalfOverflowBetweenSpeedoPulses            == 0x0031;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
CruiseControlVar                                           == 0x0028;MPScan;CCVAR0;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
; IPL = Illuminate Power Loss. These are errors severe enough to alert the driver
; IPL 1
CruiseControlVar1                                          == 0x003B;MPScan;CCVAR1;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
    b45_MapStuck		= $%10000000	; Map Stuck
    b45_TpsBadSignal		= $%01000000	; Throttle
    b45_MapBadSignal		= $%00100000	; MapVolts
    b45_Bad_BatVolts		= $%00010000	; BatVolts
    b45_bit3			= $%00001000	;
    b45_BattNotCharging 	= $%00000100	; BatVoltsNotNearTarget
    b45_BadCoolantTemp		= $%00000010	; Cool Volts
    b45_BadChargeTemp		= $%00000001	; ChargeVolts
; IPL 2
CruiseControlVar2                                          == 0x003C;MPScan;CCVAR2;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
    b46_bit7			= $%10000000	;
    b46_MajorFault		= $%01000000	; Major Fault
    b46_bit5			= $%00100000	;
    b46_InjectorFault		= $%00010000	; Fuel Injector Fault
    b46_WGSolFault		= $%00001000	; Map Wastegate
    b46_bit2			= $%00000100	; Inj?
    b46_bit1			= $%00000010	; Inj?
    b46_bit0			= $%00000001	; Inj?
CruiseControlVar3                                          == 0x003D;MPScan;CCVAR3;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
    b47_MapOK			= $%10000000	; Map OK
    b47_bit6			= $%01000000	;
    b47_bit5			= $%00100000	; Used for?
    b47_bit4			= $%00010000	; Used for ?
    b47_Injectors		= $%00001000	; FuelInjector fault
    b47_Alternator		= $%00000100	; Alternator fault
    b47_bit1			= $%00000010	; Used for ?
    b47_AisFail 		= $%00000001	; AIS fail
CruiseControlVar4                                          == 0x003E;MPScan;CCVAR4;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
CruiseControlVar6                                          == 0x0040;MPScan;CCVAR6;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
CruiseSpeedSetpoint                                        == 0x003A;MPScan;CRSSPD;byte;mph;;0.00;100.00;25.00;10.00;1.00;0.00;1,024.00;gauge-a
CruiseStatus                                               == 0x002F;MPScan;CRSTAT;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
CurrentAisPosition                                         == 0x000D;MPScan;AISPOS;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
CurrentWastegateDutyCycle                                  == 0x000A;MPScan;WGDC;byte;%;0.0;0.00;100.00;10.00;1.00;1.00;0.00;127.50;gauge-d
Cylinder1Retard                                            == 0x00A2;MPScan;RET1;byte;deg;0.0;0.00;31.00;255.00;255.00;1.00;0.00;127.00;gauge-a
    b4e_bit7			= $%10000000	;
    b4e_bit6			= $%01000000	;
    b4e_bit5			= $%00100000	;
    b4e_bit4			= $%00010000	;
    b4e_bit3			= $%00001000	;
    b4e_bit2			= $%00000100	;
    b4e_bit1			= $%00000010	;
    b4e_bit0			= $%00000001	;
Cylinder2Retard                                            == 0x00A1;MPScan;RET2;byte;deg;0.0;0.00;31.00;255.00;255.00;1.00;0.00;127.00;gauge-a
    b4f_OffIdle 		= $%10000000	; Throttle Pressed
    b4f_UpdatedMINTHR		= $%01000000	; Minimum Throttle Value has been updated with an actual value
    b4f_OpenLoop		= $%00100000	; Not In Closed Loop ;Oxygen Sensor Stuck
    b4f_O2Valid 		= $%00010000	; Oxygen Sensor Has Been Outside .75V to .29V Range
    b4f_PartThrottle		= $%00001000	; Throttle Lightly Pressed
    b4f_O2Rich			= $%00000100	; Oxygen Sensor on the Rich Side
    b4f_PTEisMaxed		= $%00000010	; Part Throttle Enrichment is maxed
    b4f_FullThrottle		= $%00000001	; Throttle Floored
Cylinder3Retard                                            == 0x00A3;MPScan;RET3;byte;deg;0.0;0.00;31.00;255.00;255.00;1.00;0.00;127.00;gauge-a
    b50_Purge			= $%10000000	; Canister Purge
    b50_FallToIdle		= $%01000000	; Engine Speed Too High to be Idling
    b50_InMotion		= $%00100000	; Something to do with vehicle moving
    b50_StayOpenLoop		= $%00010000	; Dont Try Closed Loop
    b50_IdleSpeedMode		= $%00001000	; Dont Control Idle Speed (if clear dont control AIS, if set dont control idle with Injectors)
    b50_OpenLoop		= $%00000100	; Currently Open Loop
    b50_FuelCurveACToggle	= $%00000010	; Toggles the temp enrichment fuel curve from A to C
    b50_BadO2			= $%00000001	; Oxygen Sensor Bad
Cylinder4Retard                                            == 0x00A4;MPScan;RET4;byte;deg;0.0;0.00;31.00;255.00;255.00;1.00;0.00;127.00;gauge-a
    b51_SparkEngineNotRunning	= $%10000000	; Spark - Engine Not Running
    b51_bit6			= $%01000000	; AIS Stuff
    b51_BaroSolEnergized	= $%00100000	; 
    b51_ASDon			= $%00010000	; ASD ON
    b51_SpeedUnder40		= $%00001000	; SPEED GREATER THAN 40 MPH
    b51_Past12secRunning	= $%00000100	; ENGINE RUNNING MORE THAN 12 sec OR KEY ON FOR MORE THAN 12 sec
    b51_BladePassedSensor_INSYC3	= $%00000010	; WINDOW BLADE HAS PASSED THROUGH DISTRIBUTOR SYNC SENSOR
    b51_EndOfBlade_SYCLOW		= $%00000001	; END OF ANY BLADE AT DISTRIBUTOR REF SENSOR
DCCOR1_AdaptiveWastegateCellBelowMAPPT                     == 0x0003;MPScan;DCCOR1;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
    b52_PTU_B 		        = $%10000000	
    b52_PTU_A 		        = $%01000000
    b52_WGDC 		        = $%00100000
    b52_EMR 		        = $%00010000
    b52_OverRev 		= $%00001000	; OverRevving
    b52_FuelOff 		= $%00000100	; Shut Off Fuel
    b52_DRBToggle2		= $%00000010	; DRBII Toggle
    b52_DRBToggle1		= $%00000001	; DRBII Toggle
DCCOR2_AdaptiveWastegateCellToDCRPM1                       == 0x0004;MPScan;DCCOR2;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
    b53_bit7			= $%10000000	;
    b53_bit6			= $%01000000	;
    b53_bit5			= $%00100000	; Coil Test
    b53_bit4			= $%00010000	;
    b53_bit3			= $%00001000	;
    b53_bit2			= $%00000100	;
    b53_PurgeSolenoid		= $%00000010	; Purge Solenoid
    b53_bit0			= $%00000001	; Coil Test
DCCOR3_AdaptiveWastegateCellToDCRPM2                       == 0x0005;MPScan;DCCOR3;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
    b54_FuelEngineNotRunning	= $%10000000	; Fuel - Engine Not Running
    b54_BigMapChange		= $%01000000	; Significant MAP Change
    b54_JustStarted		= $%00100000	; Engine Just Started
    b54_Starting		= $%00010000	; Use Starting Injector PW Calculations (instead of Running Injector PW Calculations)
    b54_BaroOkEngineStopped	= $%00001000	; Take Baro Reading Straight From MAP Since Engine Not Running
    b54_Uncranked		= $%00000100	; Engine Not Cranked Since 
    b54_DisableNormalDwell	= $%00000010	; Normal Dwell Disable
    b54_NeedSetup		= $%00000001	; System Needs To Run Setup Routine
DCCOR4_AdaptiveWastegateCellToDCRPM3                       == 0x0006;MPScan;DCCOR4;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
    b55_BoostOver5psi		= $%10000000	; Boost Greater than 5 PSI
    b55_WastegateDC		= $%01000000	; Current WasteGate Duty Cycle
    b55_DistSync		= $%00100000	; Distributor Sync Value
    b55_UseSparkScatter 	= $%00010000	; Use Spark Scatter
    b55_SearchBladeEndRef_INSYNC	= $%00001000	; Search for end of window blade on Reference Signal
    b55_O2Enable		= $%00000100	; Oxygen Sensor Enable or something with CAM position bits not in sync with distributor
    b55_InjectorB		= $%00000010	; CAM Position Bit 1 - this bit controls InjectorB
    b55_InjectorA		= $%00000001	; CAM Position Bit 0 - this bit controls InjectorA
    b55_InjectorAandB		= $%00000011	; Both b52_InjectorB and b52_InjectorA
DCCOR5_AdaptiveWastegateCellAboveDCRPM3                    == 0x0007;MPScan;DCCOR5;byte;%;0.0;-25.00;25.00;1.00;1.00;1.00;-25.00;25.00;gauge-a
    b56_bit7	                = $%10000000    ;
    b56_bit6	                = $%01000000    ;
    b56_bit5			= $%00100000    ; Used for ?
    b56_BadSpeedo1		= $%00010000	; Stuck Off
    b56_BadSpeedo2		= $%00001000	; Stuck On
    b56_BadASD			= $%00000100	; ASD Test
    b56_Alternator1		= $%00000010	; AlternatorTest
    b56_Alternator2		= $%00000001	; AlternatorTest
    b56_AlternatorBits		= $%00000011
DesiredNewAisPosition                                      == 0x0095;MPScan;AISNEW;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
DistributorFallingEdgePulsewidth_HB                        == 0x004A;MPScan;DISTPW;word;mSec;0.00;0.00;65.00;1.00;1.00;1.00;0.00;65.00;graph
DistributorFallingEdgePulsewidth_LB                        == 0x004B;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
DRBOffsetStored_HB                                         == 0x00B9;MPScan;DRBOFS1;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
DRBOffsetStored_LB                                         == 0x00BA;MPScan;DRBOFS2;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
DRBPointer1                                                == 0x00BC;MPScan;DRBPTR1;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
DRBPointer2                                                == 0x00BD;MPScan;DRBPTR2;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
DRBSerialMode                                              == 0x00BE;MPScan;DRBMODE;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
DwellTime_HB                                               == 0x00AC;MPScan;DWELL;word;mSec;0.00;0.00;65.00;1.00;1.00;1.00;0.00;65.00;graph
DwellTime_LB                                               == 0x00AD;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a

; block of 4 bytes for MAP changes:
Block_MAP                                                  == 0x0061
EGRVar1                                                    == 0x00B0;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
EGRVar2                                                    == 0x00B1;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
EGRVar3                                                    == 0x00B2;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
EGRVar4                                                    == 0x00B3;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a

; block of 4 bytes for TPS changes:
Block_TPS                                                  == 0x0065
EGRVar5                                                    == 0x00B4;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
EGRVar6                                                    == 0x00B5;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
EGRVar7                                                    == 0x00B6;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
EngineRpm_HB                                               == 0x005D;MPScan;RPM;word;rpm;0;0.00;8,000.00;1,000.00;100.00;1.00;0.00;8,160.00;gauge-a
EngineRpm_LB                                               == 0x005E;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
EngineRunningTimeBeforeStall                               == 0x0082;MPScan;ERTSTAL;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
EngineRunningTimeMaxFF                                     == 0x0081;MPScan;ERTMAX;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
ErrorBitRegister0                                          == 0x001E;MPScan;ERR0;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
ErrorBitRegister1                                          == 0x001F;MPScan;ERR1;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
ErrorBitRegister2                                          == 0x0020;MPScan;ERR2;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
ErrorBitRegister3                                          == 0x0021;MPScan;ERR3;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
ErrorBitRegisterStored0                                    == 0x0022;MPScan;ERS0;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
ErrorBitRegisterStored1                                    == 0x0023;MPScan;ERS1;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
ErrorBitRegisterStored2                                    == 0x0024;MPScan;ERS2;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
ErrorBitRegisterStored3                                    == 0x0025;MPScan;ERS3;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
ErrorBitsAssociatedWithPIA1AndReg1eTo25_HB                 == 0x0041;MPScan;ERRPIA1;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
ErrorBitsAssociatedWithPIA1AndReg1eTo25_LB                 == 0x0042;MPScan;ERRPIA2;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
ERRORCODERESETTIMERIN_UN_ERRORCODEIN_LN_VAR                == 0x0048;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
ErrorCodeUpdateKeyOnCount                                  == 0x0026;MPScan;ERRUPD1;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Factor_ACVDCY_CurveACurveCDecayAfterRunModeReached         == 0x0073;MPScan;ACVDCY;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Factor_DecelLeanoutWhenMAPDecreasing                       == 0x0078;MPScan;FCTDClM;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Factor_DecelLeanoutWhenThrottleDecreasing                  == 0x0079;MPScan;FCTDClT;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Factor_LeanoutOrEnrichTime_MAP                             == 0x0064;MPScan;FCTMAP;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-d
Factor_LeanoutOrEnrichTime_TPS                             == 0x0068;MPScan;FCTTPS;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Factor_StartFuelDecayIntoRunFuel                           == 0x0076;MPScan;FCTSTF;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
FinalAdvanceActual                                         == 0x00D0;MPScan;FINADV;byte;deg;0.0;-64.00;64.00;255.00;255.00;1.00;-64.00;64.00;gauge-d
InjectorLatency                                            == 0x0092;MPScan;INJLAT;byte;mSec;0.00;0.00;4.10;1.00;1.00;1.00;0.00;4.10;gauge-a
InjectorPulsewidth_HB                                      == 0x005B;MPScan;INJPW;word;mSec;0.00;0.00;49.15;10.00;1.00;1.00;0.00;49.15;gauge-d
InjectorPulsewidth_LB                                      == 0x005C;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
INTERRUPT_COUNTER_VAR                                      == 0x00D6;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
KeyOnOrEngineRunningTime                                   == 0x007F;MPScan;ENGRUN;byte;sec;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
KnockSensorThreshold                                       == 0x00A7;MPScan;KNKTHR;byte;Volts;0.0;0.00;5.00;255.00;255.00;1.00;0.00;5.00;gauge-a
KnockVolts                                                 == 0x0070;MPScan;KNKVLT;byte;volts;0.0;0.00;5.00;1.00;1.00;1.00;0.00;5.00;gauge-d
L0000                                                      == 0x0000;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L0001                                                      == 0x0001;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00D1                                                      == 0x00D1;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00DA                                                      == 0x00DA;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00DB                                                      == 0x00DB;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00DC                                                      == 0x00DC;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00DD                                                      == 0x00DD;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00DE                                                      == 0x00DE;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00DF                                                      == 0x00DF;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00E0                                                      == 0x00E0;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00E1                                                      == 0x00E1;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00E2                                                      == 0x00E2;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00E3                                                      == 0x00E3;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00E4                                                      == 0x00E4;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00E5                                                      == 0x00E5;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00E6                                                      == 0x00E6;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00E7                                                      == 0x00E7;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00E8                                                      == 0x00E8;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00E9                                                      == 0x00E9;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00EA                                                      == 0x00EA;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00EB                                                      == 0x00EB;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00EC                                                      == 0x00EC;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00ED                                                      == 0x00ED;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00EE                                                      == 0x00EE;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00EF                                                      == 0x00EF;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00F0                                                      == 0x00F0;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00F1                                                      == 0x00F1;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00F2                                                      == 0x00F2;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00F3                                                      == 0x00F3;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00F4                                                      == 0x00F4;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00F5                                                      == 0x00F5;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00F6                                                      == 0x00F6;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00F7                                                      == 0x00F7;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00F8                                                      == 0x00F8;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00F9                                                      == 0x00F9;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00FA                                                      == 0x00FA;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00FB                                                      == 0x00FB;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00FC                                                      == 0x00FC;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00FD                                                      == 0x00FD;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
L00FF                                                      == 0x00FF;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
LastDistributorFallingEdgeTime                             == 0x004D;MPScan;LDISTPW;byte;mSec;0.00;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-d
MapBlockScratchValue                                       == 0x0062;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
MapValue                                                   == 0x0063;MPScan;MAP;byte;psi;0.0;0.00;30.00;5.00;1.00;1.00;0.00;29.40;gauge-a
MapVolts                                                   == 0x0060;MPScan;MAPVLT;byte;volts;0.0;0.00;5.00;1.00;1.00;1.00;0.00;5.00;gauge-d
MaxRetardFromMAP                                           == 0x00A5;MPScan;MAXRET;byte;;;0.00;127.00;255.00;255.00;1.00;0.00;127.00;gauge-a
MinimumTimerCountBeforeMainloopCanContinue                 == 0x0084;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
MINTHR_LowestSessionTPS                                    == 0x0002;MPScan;MINTHR;byte;volts;0.00;0.00;5.00;1.00;1.00;1.00;0.00;5.00;gauge-a
NO2Retard                                                  == 0x00CD;MPScan;NO2RET;byte;deg;0.0;0.00;128.00;255.00;255.00;1.00;0.00;128.00;gauge-d
O2SensorValue                                              == 0x00CF;MPScan;O2SENS;byte;Volts;0.0;0.00;5.00;1.00;1.00;1.00;0.00;5.00;gauge-a
Pattern_SparkCut                                           == 0x00D2;MPScan;PTNSPK;byte;rpm;0.0;0.00;8,000.00;8.00;32.00;1.00;0.00;8,192.00;gauge-a
    sw1_PNswitch		= $%10000000	; Park/Neutral switch
    sw1_Brake			= $%01000000	; Brake Switch
    sw1_DistSync		= $%00100000	; Distributor Sync
    sw1_ACclutch		= $%00010000	; A/C Clutch input
    sw1_CruiseResume		= $%00001000	; Cruise Resume
    sw1_CruiseOnOff		= $%00000100	; Cruise On/Off
    sw1_CruiseSet		= $%00000010	; Cruise Set
    sw1_B1Volt			= $%00000001	; B1 Voltage Sense
PIA1_A_Buffer                                              == 0x002C;MPScan;PIAB;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
    sw2_PNswitch		= $%10000000	; Park/Neutral switch
    sw2_Brake			= $%01000000	; Brake Switch
    sw2_DistSync		= $%00100000	; Distributor Sync
    sw2_ACclutch		= $%00010000	; A/C Clutch input
    sw2_CruiseResume		= $%00001000	; Cruise Resume
    sw2_CruiseOnOff		= $%00000100	; Cruise On/Off
    sw2_CruiseSet		= $%00000010	; Cruise Set
    sw2_B1Volt			= $%00000001	; B1 Voltage Sense
PointerIntoAdaptiveMemory                                  == 0x008A;MPScan;MEMPTR;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
PreviousBoostOverBaro                                      == 0x00C9;MPScan;PREVBST;byte;psi;0.0;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
PreviousVehicleSpeed_HB                                    == 0x0032;MPScan;PRVSPD;word;mph;0.0;0.00;200.00;25.00;10.00;1.00;0.00;1,024.00;gauge-a
PreviousVehicleSpeed_LB                                    == 0x0033;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
PTU_MapTemp                                                == 0x00D7;MPScan;PTUMAP;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Pulsewidth_PartThrottleEnrichment_HB                       == 0x007B;MPScan;PTEPW;word;mSec;0.00;0.00;49.15;10.00;1.00;1.00;0.00;49.15;gauge-a
    bbe_FastSerial		= $%10000000	; Hi-Speed Logger flag
    bbe_ByteMode		= $%01000000	; Byte-Mode Serial code Download (apprently special test for development/S60)
    bbe_TestType3		= $%00100000	; Test type indicator (1-, 2-, or 3-byte)
    bbe_TestType2		= $%00010000	; Test type indicator (1-, 2-, or 3-byte)
    bbe_bit3			= $%00001000	; The bottom half is used as a loop counter for timeout purposes
    bbe_bit2			= $%00000100	;
    bbe_bit1			= $%00000010	;
    bbe_bit0			= $%00000001	;
    bbe_top			= $%11110000	; all control bits
    bbe_bottom			= $%00001111	; all counter bits
Pulsewidth_PartThrottleEnrichment_LB                       == 0x007C;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
RawAirFuelSensInput                                        == 0x006C;MPScan;O2VLT;byte;volts;0.0;0.00;5.00;1.00;1.00;1.00;0.00;5.00;gauge-a
RawChargeTempVolts                                         == 0x006F;MPScan;RAWIAT;byte;volts;0.0;0.00;5.00;1.00;1.00;1.00;0.00;5.00;gauge-a
RawCoolantTempVolts                                        == 0x006E;MPScan;RAWCTS;byte;volts;0.0;0.00;5.00;1.00;1.00;1.00;0.00;5.00;gauge-a
SparkScatter                                               == 0x008C;MPScan;SPKSCAT;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
SparkScatterFuelStabilizationValue_HB                      == 0x008F;MPScan;SSFUEL;word;mSec;0.0;0.00;49,152.00;255.00;255.00;1.00;0.00;49,152.00;gauge-d
SparkScatterFuelStabilizationValue_LB                      == 0x0090;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
SpeedoSensorPulsewidth_HB                                  == 0x0035;MPScan;SDSPW;word;mSec;0.00;0.00;65.00;255.00;255.00;1.00;0.00;66.00;gauge-d
SpeedoSensorPulsewidth_LB                                  == 0x0036;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a

;CCDVar0                                                    == 0x00C8;MPScan;CCDVar;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
;    ccd_Bit7		        = $%10000000	;
;CCDTemp_HB                                                 == 0x00C9;MPScan;CCDTemp;word;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
;CCDTemp_LB                                                 == 0x00CA;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a

StartupSwitchMirror1                                       == 0x00B7;MPScan;SWTCH1;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
StartupSwitchMirror2                                       == 0x00B8;MPScan;SWTCH2;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
STOPInstruction                                            == 0x00FE;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
SumOfFuelModifiers_HB                                      == 0x0059;MPScan;FULMOD;word;%;0;0.00;100.00;25.00;10.00;1.00;0.00;100.00;gauge-d
SumOfFuelModifiers_LB                                      == 0x005A;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a

TargetBatteryVolts                                         == 0x0072;MPScan;TGTBAT;byte;volts;0.0;0.00;16.00;4.00;1.00;1.00;0.00;16.00;gauge-a
TargetIdleSpeed_HB                                         == 0x0057;MPScan;TGTIDL;word;rpm;0;0.00;2,000.00;500.00;100.00;1.00;0.00;8,160.00;gauge-d
TargetIdleSpeed_LB                                         == 0x0058;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a

;CCDFuelOutput_HB                                          == 0x00CD;MPScan;CCDFuel;word;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
;CCDFuelOutput_LB                                          == 0x00CE;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
;CCDFlags1                                                 == 0x00CF;MPScan;CCD_F1;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
;CCDFlags2                                                 == 0x00D0;MPScan;CCD_F2;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
;CCDFlags3                                                 == 0x00D1;MPScan;CCD_F3;Byte;;;0;255;255;255;1;0;255;Gauge-A
;CCDFlags4                                                 == 0x00D2;MPScan;CCD_F4;Byte;;;0;255;255;255;1;0;255;Gauge-A

Temp0                                                      == 0x00BF;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Temp1                                                      == 0x00C0;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Temp2                                                      == 0x00C1;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Temp3                                                      == 0x00C2;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Temp4                                                      == 0x00C3;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a

Temp5                                                      == 0x00C4;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
    Turbonator_SparkCut	        = $%10000000    ; Turbonator - Spark-based rev limiter
    Turbonator_Staging	        = $%01000000    ; Turbonator - staging limiter is active
    Turbonator_FuelOff          = $%00100000    ; Turbonator - Fuel-based rev limiter
    Turbonator_OverRev          = $%00010000    ; over rev - replaced the original flag for simplicity
    Turbonator_AntiLag          = $%00001000    ; AntiLag is active
    Turbonator_Bit2             = $%00000100    ; Open
    Turbonator_AllowSpark       = $%00000010    ; Allow spark for only this cycle
    Turbonator_DecelFuelCut     = $%00000001    ; use decel fuel cut

Temp6                                                      == 0x00C5;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Temp7                                                      == 0x00C6;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Temp8                                                      == 0x00C7;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_AcClutchEngageRestrictionTimer                       == 0x0097;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a

; reserved for stack ?
Timer_AcCutout                                             == 0x0098;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_AisChanges                                           == 0x0096;MPScan;TIMACCT;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_AisOrO2Sensor                                        == 0x0099;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_AlternatorDutyCycle                                  == 0x0083;MPScan;TIMALTD;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_BaroReadInterval                                     == 0x00A8;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_BaroReadRpmConditionsSatisfied                       == 0x00A9;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_BoostErrTimer                                        == 0x000B;MPScan;TIMBSE;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_BoostInErrorTimer                                    == 0x00C8;MPScan;TMBSTER;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_BoostTimer                                           == 0x0009;MPScan;TIMBST;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_CLTIME_ClosedLoopTimer                               == 0x0086;MPScan;CLTIME;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_CountdownFromStartRunForAisFeedback                  == 0x007E;MPScan;TIMCNTD;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_CruiseDecelerate                                     == 0x0039;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_DacalCountdown                                       == 0x0008;MPScan;TDACAL;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_DelayBeforeUpdating_MINTHR                           == 0x0069;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_FuelMonitorOutputTimer_HB                            == 0x00AE;MPScan;FULMON;word;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_FuelMonitorOutputTimer_LB                            == 0x00AF;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_MinimumFanRun                                        == 0x009C;MPScan;TIMMINF;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_NormalDwell                                          == 0x009D;MPScan;TIMDWL;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_O2CNTR_CountdownFromAbove196FtoEnableClosedLoop      == 0x0088;MPScan;O2CNTR;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_O2InhibitSwitchingRichIdleToClosedLoop               == 0x007A;MPScan;TIMO2IH;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_O2MiddleDiagnostics                                  == 0x00AB;MPScan;TIMO2MD;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_O2ToggleDuration                                     == 0x0094;MPScan;TIMO2TG;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_OffThrottleFuelEnrich                                == 0x0091;MPScan;TIMOTE;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_OpenLoopFraction                                     == 0x0077;MPScan;TIMOLF;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_Over5PsiBoostMaxFF                                   == 0x009F;MPScan;TIM5PSI;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_OverboostCountdown                                   == 0x009E;MPScan;TIMOBST;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_RadSteamingCountdown                                 == 0x009B;MPScan;TIMRAD;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
Timer_ThermostatDiagnostics                                == 0x00AA;MPScan;TIMSTAT;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
TimerOverflowsBetweenDistPulses                            == 0x0049;MPScan;TOFLDS;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-d
TimerOverflowsBetweenSpeedoPulses                          == 0x0034;MPScan;SPDOFLO;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-d
TpsBlockScratchValue                                       == 0x0066;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
TpsVolts                                                   == 0x0067;MPScan;TPSVLT;byte;volts;0.0;0.00;5.00;1.00;1.00;1.00;0.00;5.00;gauge-a
TPSVolts_11msUpdate                                        == 0x006D;MPScan;TPS11;byte;volts;0.0;0.00;5.00;1.00;1.00;1.00;0.00;5.00;gauge-a
Turbonator_Flags                                           == 0x00D5;MPScan;FLAGTRB;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;bit
ValueFromAdaptiveMemory                                    == 0x008B;MPScan;MEMVAL;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
VehicleSpeed_HB                                            == 0x0037;MPScan;VEHSPD;word;mph;0;0.00;200.00;25.00;10.00;1.00;0.00;1,024.00;gauge-a
VehicleSpeed_LB                                            == 0x0038;MPScan;None;byte;;;0.00;255.00;255.00;255.00;1.00;0.00;255.00;gauge-a
WastegateDutyCycleIncreaseFromKnock                        == 0x00A6;MPScan;WGDCKNK;byte;%;0;0.00;100.00;1.00;1.00;1.00;0.00;127.50;gauge-a

; CPU (register bits)

CPU_PortA						  == 0x1000
    CPU_PortA_bit7		    = $%10000000    ;
    CPU_PortA_bit6		    = $%01000000    ;
    CPU_PortA_InjectorB 	    = $%00100000    ; Injector B
    CPU_PortA_InjectorA 	    = $%00010000    ; Injector A
    CPU_PortA_IgnCoil		    = $%00001000    ; Ignition Coil
    CPU_PortA_DistRef	            = $%00000100    ; Distributor
    CPU_PortA_Speedo		    = $%00000010    ; Speedo
    CPU_PortA_bit0		    = $%00000001    ;
CPU_L1001_Reserved					  == 0x1001
CPU_PortIOControl					  == 0x1002
CPU_PortC						  == 0x1003
CPU_PortB						  == 0x1004
CPU_PortCL						  == 0x1005
CPU_L1006Reserved					  == 0x1006
CPU_PortC_DataDirection					  == 0x1007
CPU_PortD						  == 0x1008
CPU_PortD_DataDirection					  == 0x1009
CPU_PortE						  == 0x100a
CPU_TimerForceCompare					  == 0x100b
;	  Bit 7 - FOC1: Force Output Compare, but does not generate interrupt
;	  Bit 6 - FOC2:
;	  Bit 5 - FOC3:
;	  Bit 4 - FOC4:
;	  Bit 3 - FOC5:
;	  Bit 2 - 0
;	  Bit 1 - 0
;	  Bit 0 - 0
CPU_OutputCompare1Mask					  == 0x100c
;	  Bit 7 - OC1M7:
;	  Bit 6 - OC1M6:
;	  Bit 5 - OC1M5:
;	  Bit 4 - OC1M4:
;	  Bit 3 - OC1M3:
;	  Bit 2 - 0
;	  Bit 1 - 0
;	  Bit 0 - 0
CPU_OutputCompare1D					  == 0x100d
;	  Bit 7 - OC1D7: references PA7/PA1
;	  Bit 6 - OC1D6: references PA6/OC2
;	  Bit 5 - OC1D5: references PA5/OC3
;	  Bit 4 - OC1D4: references PA4/OC4
;	  Bit 3 - OC1D3: references PA3/PC5
;	  Bit 2 - 0
;	  Bit 1 - 0
;	  Bit 0 - 0
CPU_TimerCounterRegHigh					  == 0x100e
CPU_TimerInputCapture1_Distributor			  == 0x1010
CPU_TimerInputCapture2_Speedometer			  == 0x1012
CPU_Timer_OC1						  == 0x1016
CPU_Timer_OC2_Wastegate					  == 0x1018
CPU_Timer_OC3_InjectorBDriver				  == 0x101a
CPU_Timer_OC4_InjectorADriver				  == 0x101c
CPU_Timer_OC5_Dwell					  == 0x101e
CPU_TimerControlReg1					  == 0x1020
;		  Output Compare Pin Control
;	  Bit 7 - OM2:	   M0, L0 = OCx does not affect pin (OC1 still may)
;	  Bit 6 - OL2:	   M0, L1 = Toggle OCx pin on successful compare
;	  Bit 5 - OM3:	   M1, L0 = Clear OCx pin on successful compare
;	  Bit 4 - OL3:	   M1, L1 = Set OCx pin on successful compare
;	  Bit 3 - OM4:
;	  Bit 2 - OL4:
;	  Bit 1 - OM5:
;	  Bit 0 - OL5:
CPU_TimerControlReg2					  == 0x1021
    CPU_TCR2_Bit7	    = $%10000000
    CPU_TCR2_Bit6	    = $%01000000    
    CPU_TCR2_EDG1B 	    = $%00100000  
    CPU_TCR2_EDG1A 	    = $%00010000  
    CPU_TCR2_EDG2B	    = $%00001000   
    CPU_TCR2_EDG2A	    = $%00000100   
    CPU_TCR2_EDG3B	    = $%00000010   
    CPU_TCR2_EDG3A	    = $%00000001
;	  Bit 7 - 0
;	  Bit 6 - 0
;	  Bit 5 - EDG1B: Input capture edge configuration:
;	  Bit 4 - EDG1A:    0 0 = capture disabled
;	  Bit 3 - EDG2B:    0 1 = capture rising edges only
;	  Bit 2 - EDG2A:    1 0 = capture falling edges only
;	  Bit 1 - EDG3B:    1 1 = capture both rising and falling
;	  Bit 0 - EDG3A:
CPU_TimerInterruptMask1					  == 0x1022
;	  Bit 7 - OC1I: Input Capture Enables
;	  Bit 6 - OC2I:
;	  Bit 5 - OC3I:
;	  Bit 4 - OC4I:
;	  Bit 3 - OC5I:
;	  Bit 2 - IC1I:
;	  Bit 1 - IC2I:
;	  Bit 0 - IC3I:
CPU_TimerInterruptFlag1					  == 0x1023
    CPU_TIFlag1_OutputCompare1	    = $%10000000    ;
    CPU_TIFlag1_OC2Wastegate	    = $%01000000    ; Wastegate
    CPU_TIFlag1_OutputCompare3 	    = $%00100000    ; Injector B
    CPU_TIFlag1_OutputCompare4 	    = $%00010000    ; Injector A
    CPU_TIFlag1_OC5Dwell	    = $%00001000    ; Ignition Coil
    CPU_TIFlag1_IC1Distributor	    = $%00000100    ; Distributor
    CPU_TIFlag1_IC2SDSSignal	    = $%00000010    ; Speedo
    CPU_TIFlag1_InputCompare3	    = $%00000001    ;
;	  Bit 7 - OC1F: Input Capture Flags
;	  Bit 6 - OC2F:
;	  Bit 5 - OC3F:
;	  Bit 4 - OC4F:
;	  Bit 3 - OC5F:
;	  Bit 2 - IC1F:
;	  Bit 1 - IC2F:
;	  Bit 0 - IC3F:
CPU_TimerInterruptMask2					  == 0x1024
;	  Bit 7 - TOI:	 Timer Overflow Interrupt Enable
;	  Bit 6 - RTII:  Real Time Interrupt Enable
;	  Bit 5 - PAOVI: Pulse accumulator overflow interrupt enable
;	  Bit 4 - PAII:  Pulse accumulator input edge interrupt enable
;	  Bit 3 - 0
;	  Bit 2 - 0
;	  Bit 1 - PR1:	 Timer Prescaler Select: 00=1, 01=4, 10=8, 11=16
;	  Bit 0 - PR0:
CPU_PulseAccumulatorControl				  == 0x1026
;	  Bit 7 - DDRA7: Data direction control for port A bit 7 (0=in, 1=out)
;	  Bit 6 - PAEN:  Pulse accumulator Enable (0=disable, 1=enable)
;	  Bit 5 - PAMOD: Pulse accumulator mode (0=external even, 1=gated time accum)
;	  Bit 4 - PEDGE: Pulse accumulator edge (0=falling edge, 1=rising edge)
;	  Bit 3 - 0
;	  Bit 2 - 0
;	  Bit 1 - RTR1: Rate selects: 00 = /1 = 4.1ms/pulse, 01 = /2 = 8.19ms/pulse
;	  Bit 0 - RTR0: 	      10 = /4 = 16ms/pulse,  11 = /8 = 32ms/pulse
CPU_SerialPeripheralControl				  == 0x1028
CPU_SerialPeripheralStatus				  == 0x1029
;	  Bit 7 - SPIF - SPI Transfer complete flag
;	  Bit 6 - WCOL - Write collision error flag
;	  Bit 5 - 0
;	  Bit 4 - MODF - Mode fault error flag
;	  Bit 3 - 0
;	  Bit 2 - 0
;	  Bit 1 - 0
;	  Bit 0 - 0
CPU_SerialPeripheralDataIO				  == 0x102a
CPU_SerialBaudRate					  == 0x102b
;	  Bit 7 - TCLR: (test bit)
;	  Bit 6 - 0
;	  Bit 5 - SCP1: SCI Baud rate prescale selects
;	  Bit 4 - SCP0: 00= /1 = max125k, 01= /3 = max42k, 10= /4 = max32k, 11= /13 = max9600baud
;	  Bit 3 - RCKB: (test bit)
;	  Bit 2 - SCR2:
;	  Bit 1 - SCR1:
;	  Bit 0 - SCR0:
; To achieve 977 baud, byte=$25
; To achieve 1200 baud, byte $33
; To achieve 9600 baud, byte = $30
; To achieve 62500 baud, byte = $01
;
CPU_SerialControl1					  == 0x102c
CPU_SerialControl2					  == 0x102d
CPU_SerialStatus					  == 0x102e
CPU_SerialData						  == 0x102f
CPU_A2DControlReg					  == 0x1030
;	  Bit 7 - CCF:	Conversions Complete Flag
;	  Bit 6 - 0
;	  Bit 5 - SCAN: 0=perform 4 conversions. 1=continuous conversions
;	  Bit 4 - MULT: 0=single channel, 1=multi-channel
;	  Bit 3 - CD: These bits select which channel(s) to convert
;	  Bit 2 - CC:
;	  Bit 1 - CB:
;	  Bit 0 - CA:
CPU_A2DResults1						  == 0x1031
CPU_A2DResults2						  == 0x1032
CPU_A2DResults3						  == 0x1033
CPU_A2DResults4						  == 0x1034
CPU_BlockProtReg					  == 0x1035
CPU_SysConfigOptionReg					  == 0x1039
;	  Bit 7 - ADPU:
;	  Bit 6 - CSEL: 1=use alternate charge pump for EEPROM and A/D
;	  Bit 5 - IRQE: 1=configure IRQ for edge sensitive operation only, otherwise level sensitive
;	  Bit 4 - DLY:	1=enable oscillator startup delat (designed to allow crystal to stabilize)
;	  Bit 3 - CME:
;	  Bit 2 - 0
;	  Bit 1 - CR1:	Watchdog Timer Rate Select
;	  Bit 0 - CR0:	at 8MHz, 00=16ms, 01=65ms, 10=262ms, 11=1.049s
CPU_ArmResetCopTimerReg					  == 0x103a
CPU_EEPROMControlReg					  == 0x103b
;	  Bit 7 - ODD
;	  Bit 6 - EVEN
;	  Bit 5 - 0
;	  Bit 4 - BYTE
;	  Bit 3 - ROW
;	  Bit 2 - ERASE
;	  Bit 1 - EELAT
;	  Bit 0 - EEPGM
CPU_HighPriorityInterruptMask				  == 0x103c
;	  Bit 7 - RBOOT: Read Bootstrap ROM (can be written only while SMOD=1) 1=bootstrap ROM at $bf40-$bfff
;	  Bit 6 - SMOD:  Special Mode (can be written to zero but not back to one) 1=special mode in effect
;	  Bit 5 - MDA:	 Mode A Select (can be written only while SMOD=1) 1=normal expanded, 0=normal singlechip
;	  Bit 4 - IRV:	 Internal Read Visibility (can be written only while SMOD=1) 0=data from internal reads not visible on bus
;	  Bit 3 - PSEL3: for selecting which interrupt is highest priority
;	  Bit 2 - PSEL2:
;	  Bit 1 - PSEL1:
;	  Bit 0 - PSEL0:
CPU_SysInit						  == 0x103d
;	  Bit 7 - RAM3: Ram3:0 specify the upper hex digit of the RAM address, controlling
;	  Bit 6 - RAM2:        the position of the RAM in the memory map. This allows RAM
;	  Bit 5 - RAM1:        to be moved, for example, to F000-F0FF (default is 0000)
;	  Bit 4 - RAM0:
;	  Bit 3 - REG3: Reg3:0 specify the upper hex digit of the Registers address, just
;	  Bit 2 - REG2:        like the RAM. (default is 0001)
;	  Bit 1 - REG1:
;	  Bit 0 - REG0:
CPU_TestingFunctionsRegister				  == 0x103e  ; TEST1
;	  Bit 7 - TILOP:
;	  Bit 6 - 0
;	  Bit 5 - OCCR:
;	  Bit 4 - CBYP:
;	  Bit 3 - DISR:
;	  Bit 2 - FCM:
;	  Bit 1 - FCOP:
;	  Bit 0 - TCON:
CPU_SystemConfigReg					  == 0x103f

; HARDWARE (memory mapped IO)

PIA1_PortA_DataDirection			    == 0x4000
PIA1_PortA_ControlRegister			    == 0x4001
    pia1a_CruiseVent		= $%10000000	; Cruise Vent
    pia1a_CELight		= $%01000000	; Check Engine Light
    pia1a_ASDRelay		= $%00100000	; ASD Relay
    pia1a_FanRelay		= $%00010000	; Fan Relay
    pia1a_ACClutchRelay 	= $%00001000	; A/C Clutch Relay
    pia1a_PartThrotUnlock	= $%00000100	; Part Throttle Unlock
    pia1a_PurgeSolenoid 	= $%00000010	; Purge Solenoid
    pia1a_CruiseVacuum		= $%00000001	; Cruise Vacuum
PIA1_PortB_DataDirection			    == 0x4002
PIA1_PortB_ControlRegister			    == 0x4003
    pia1b_EgrSolenoid		= $%10000000	; EGR Solenoid
    pia1b_WastegateSolenoid	= $%01000000	; Wastegate Solenoid
    pia1b_BaroReadSolenoid	= $%00100000	; Baro Read Solenoid
    pia1b_EmissionLight 	= $%00010000	; Emissions Maint Reminder Light
    pia1b_bit3			= $%00001000	; AIS3
    pia1b_bit2			= $%00000100	; AIS2
    pia1b_bit1			= $%00000010	; AIS1
    pia1b_bit0			= $%00000001	; AIS0
PIA2_PortA_DataDirection			    == 0x5000
PIA2_PortA_ControlRegister			    == 0x5001
    pia2a_bit7			= $%10000000	;
    pia2a_bit6			= $%01000000	;
    pia2a_bit5			= $%00100000	;
    pia2a_bit4			= $%00010000	;
    pia2a_FuelMonitor		= $%00001000	; Fuel Monitor (Navigator)
    pia2a_Tach			= $%00000100	; Tach Signal
    pia2a_CCDBus		= $%00000010	; CCD Bus chip enable
    pia2a_bit0			= $%00000001	;
PIA2_PortB_DataDirection			    == 0x5002
PIA2_PortB_ControlRegister			    == 0x5003
    pia2b_CoolantTempRange	= $%10000000	; Coolant Temp Range Bit
    pia2b_bit6			= $%01000000	;
    pia2b_KnockCap		= $%00100000	; Clear Knock Voltage Storage Cap
    pia2b_AlternatorField	= $%00010000	; Alternator field control
    pia2b_OC1Toggle		= $%00001000	; OC1 indicator toggle
    pia2b_bit2			= $%00000100	;
    pia2b_IgnCoilDriverSense	= $%00000010	; Ignition Coil Driver Sense
    pia2b_InjectorDriverSense	= $%00000001	; Fuel Injector Driver Sense
SwitchPortAccessReg				    == 0x6000
    swp_PNswitch		= $%10000000	; Park/Neutral switch
    swp_Brake			= $%01000000	; Brake Switch
    swp_DistSync		= $%00100000	; Distributor Sync
    swp_ACclutch		= $%00010000	; A/C Clutch input
    swp_CruiseResume		= $%00001000	; Cruise Resume
    swp_CruiseOnOff		= $%00000100	; Cruise On/Off
    swp_CruiseSet		= $%00000010	; Cruise Set
    swp_B1Volt			= $%00000001	; B1 Voltage Sense
    
; *****************************************************************************
; load cal data
; *****************************************************************************

        .include /CalDataFile/

; *****************************************************************************
; begin code
; *****************************************************************************

; *******************************************************

	.org CodeOrg
        .msg "Assembling Code..."

; The OC1 timer is setup in 2's complement form so that it could run faster, but that the minimum is 32289us or 32.3ms

Interrupt_TimerOutputCapture1:
	ldaa #CPU_TIFlag1_OutputCompare1	    ; load a with value -10000000-
	staa CPU_TimerInterruptFlag1
	ldaa #0x10	    ; load a with value -00010000-
	staa CPU_A2DControlReg
	ldd  CPU_Timer_OC1
	addd #0x01df	    ;  479us
	cmpD CPU_TimerCounterRegHigh	; compare D
	bpl  L1000	    ; branch if plus (hi bit 0)
	ldd  CPU_TimerCounterRegHigh
	addd #0x01df	    ;  479 microseconds...
L1000:	addd #0x0002	 ;  481 microseconds...
	std  CPU_Timer_OC1
	ldaa CPU_TimerInterruptMask1	; load a with memory contents
	anda #0x7f	    ; AND a with value -01111111-
	staa CPU_TimerInterruptMask1
	ldaa Timer_AlternatorDutyCycle	  ; load a with memory contents
	inca		    ; increment a
	staa Timer_AlternatorDutyCycle	  ; store a into memory

; How the Fuel Monitor works:
; (Geoff Allan)
; The "Navigator" module in the dash receives a signal for every engine rotation. The
; length of time of this signal is dependent on the injector open duration. This gives
; the Navigator the ability to precisely calculate how much fuel is being used for a
; given time or distance, since it now has RPM and injector duty cycle in addition to
; being tapped into the speed/distance sensor. In order to
; accomodate differing injector sizes, the Conversion factor can be changed. Stock T1
; conversion factor is $03a8, if you scale the injectors you need to scale this value
; by the same amount so the Navigator retains its accuracy.

	ldd  Timer_FuelMonitorOutputTimer_HB    ; load d (a&b) with memory contents
	subd FUELTR_FuelMonitorConversionFactor    ;  (data is 03a8) = 0.936ms
	bcs  L1001	    ; branch if lower
	stD *Timer_FuelMonitorOutputTimer_HB    ; store D to RAM
	ldaa PIA2_PortA_DataDirection	 ; load a with memory contents
	eora #0x08	    ; XOR a with value -00001000-
	staa PIA2_PortA_DataDirection
L1001:	cli		    ; enable interrupts
	ldaa Timer_AlternatorDutyCycle	  ; load a with memory contents
	lsra		
	bcc  ControlAlternator	  ; branch if greater or equal
	jmp  L1013

ControlAlternator:
	ldaa ATMOffset	    ; load a with memory contents
	cmpa #0x0d	    ; compare a with value -00001101-
	beq  L1010	    ; branch if equal (zero)
	cmpa #0x14	    ; compare a with value -00010100-
	beq  L1010	    ; branch if equal (zero)
	ldx  #PIA2_PortB_DataDirection	  ; load index with value
	brset *BitFlags_54, #b54_FuelEngineNotRunning, TurnAlternatorOff    ; branch if bit(s) set
	ldab #0x11	    ; load b with value -00010001- (546 rpm) min alternator rpm?
	brset *BitFlags_56, #b56_BadASD, L1002	  ; branch if bit(s) set
	ldab #0x15	    ; load b with value -00010101- (674 rpm)
L1002:	bclr *BitFlags_56, #b56_BadASD	  ; clear bits
	cmpb EngineRpm_HB
	bhi  TurnAlternatorOff	  ; branch if higher
	bset *BitFlags_56, #b56_BadASD	  ; set bits
	ldaa CPU_A2DResults2	; load a with memory contents
	cmpa BatteryVolts    ; compare a with memory contents
	bcc  L1003	    ; branch if greater or equal
	staa BatteryVolts    ; store a into memory
L1003:	cmpa #0x41	    ; compare a with value -01000001-
	bcc  L1004	    ; branch if greater or equal
	ldab Counter_MainLoop	  ; load b with memory contents
	bitb #0x06	    ;  -00000110-
	bne  TurnAlternatorOff	  ; branch if not equal (not zero)
L1004:	brclr  0, X, #$%00010000, L1005    ; branch if bit(s) clear
	brclr  0, X, #$%00000100, L1011    ; branch if bit(s) clear
	bclr *BitFlags_56, #b56_AlternatorBits	  ; clear bits
L1005:	suba TargetBatteryVolts
	bne  L1006	    ; branch if not equal (not zero)
	brclr  0, X, #$%00010000, TurnAlternatorOn    ; branch if bit(s) clear
	bra  TurnAlternatorOff	  ; branch

L1006:	ldab #0x0e	    ; load b with value -00001110-
	bcc  L1008	    ; branch if greater or equal
	nega		    ; negate a (set high bit)
	cmpa #0x02	    ; compare a with value -00000010-
	beq  L1007	    ; branch if equal (zero)
	bcc  TurnAlternatorOn	 ; branch if greater or equal
	ldab #0x06	    ; load b with value -00000110-
L1007:	andb Timer_AlternatorDutyCycle
	beq  TurnAlternatorOff	  ; branch if equal (zero)
	bra  TurnAlternatorOn	 ; branch

L1008:	cmpa #0x02	    ; compare a with value -00000010-
	beq  L1009	    ; branch if equal (zero)
	bcc  TurnAlternatorOff	  ; branch if greater or equal
	ldab #0x06	    ; load b with value -00000110-
L1009:	andb Timer_AlternatorDutyCycle
	bne  TurnAlternatorOff	  ; branch if not equal (not zero)
TurnAlternatorOn:
	bset  0, X, #$%00010000    ; bit set
L1010:	jmp  XmitRequestedRamLocation

L1011:	ldaa BitFlags_56    ; load a with memory contents
	anda #b56_AlternatorBits	  ; AND a with value -00000011-
	cmpa #b56_AlternatorBits	  ; compare a with value -00000011-
	bcs  L1012	    ; branch if lower
	bclr *BitFlags_56, #b56_AlternatorBits	  ; clear bits
	bset *BitFlags_47, #b47_Alternator    ; set bits
	bra  TurnAlternatorOff	  ; branch

L1012:	inc  BitFlags_56
TurnAlternatorOff:
	bclr  0, X, #$%00010000    ; bit clear
	jmp  XmitRequestedRamLocation

L1013:	brset *BitFlags_AIS, #b0c_UseAIS, L1014    ; branch if bit(s) set
	lsra		
	bcs  L1010	    ; branch if lower
L1014:	ldaa BatteryVolts    ; load a with memory contents
	cmpa BTVAIS_MinVoltageForAis	; compare a with memory contents (data is 71)
	bcs  XmitRequestedRamLocation	 ; branch if lower
	brset *BitFlags_2e, #b2e_bit3, XmitRequestedRamLocation    ; branch if bit(s) set

; How the AIS drive works:
; (Geoff Allan)
; A stepper motor has a combination of electromagnetic fields that cause it to only
; rotate a tiny amount at a time. There are 4 wires going to the AIS stepper. In order
; to complete a step, there must be two distinct patterns of bits sent to these 4 wires
; after a short delay to account for the mechanical movement involved. It is possible
; that the computer has requested a new AIS position that is several steps away from the
; current position. This routine continues sending the patterns required to move the
; AIS motor to the desired new position.

AisDriveRoutine:
	ldab CountdownTimerFromKeyOn	; load b with memory contents
	bne  XmitRequestedRamLocation	 ; branch if not equal (not zero)
	ldaa #0x01	    ; load a with value -00000001-
	ldab CurrentAisPosition    ; load b with memory contents
	brclr *BitFlags_AIS, #b0c_UseAIS, L1015    ; branch if bit(s) clear
	bne  L1016	    ; branch if not equal (not zero)
	bclr *BitFlags_AIS, #b0c_UseAIS    ; clear bits
	bra  XmitRequestedRamLocation	 ; branch

L1015:	cmpb DesiredNewAisPosition
	beq  XmitRequestedRamLocation	 ; branch if equal (zero)
	bcs  L1017	    ; branch if lower
L1016:	nega		    ; negate a (set high bit)
L1017:	tab		    ; b = a
	ldx  #AISTEP_BitPatternForAisControl	; load index with value
	addb BitFlags_2d    ; b=b+memory contents
	andb #b2d_both	    ;  -00000011-
	abx		    ; add b to index
	sei		    ; disable interrupts
	stab Temp7	    ; store b into memory
	ldab BitFlags_2d    ; load b with memory contents
	andb #~b2d_both     ;  -11111100-
	orab Temp7	
	cli		    ; enable interrupts
	stab BitFlags_2d    ; store b into memory
	adda CurrentAisPosition
	staa CurrentAisPosition    ; store a into memory
	ldaa PIA1_PortB_DataDirection	 ; load a with memory contents
	anda #0xf0	    ; AND a with value -11110000-
	oraa 0x00,x	
	staa PIA1_PortB_DataDirection
	psha		    ; push a onto stack
	ldab PIA1_PortB_ControlRegister    ; load b with memory contents
	andb #~pia1b_bit2	   ;  -11111011-
	stab PIA1_PortB_ControlRegister    ; store b into memory
	sei		    ; disable interrupts
	ldd  PIA1_PortB_DataDirection
	oraa #0x0f	    ;  -00001111-
	staa PIA1_PortB_DataDirection
	jsr  Delay32uSec    ; call subroutine
	anda #0xf0	    ; AND a with value -11110000-
	staa PIA1_PortB_DataDirection
	cli		    ; enable interrupts
	tstb		
	bpl  L1018	    ; branch if plus (hi bit 0)
	jsr  IgnitionFeedOnOffTracking	  ; call subroutine
L1018:	jsr  Delay32uSec    ; call subroutine
	ldab PIA1_PortB_ControlRegister    ; load b with memory contents
	orab #pia1b_bit2	  ;  -00000100-
	stab PIA1_PortB_ControlRegister    ; store b into memory
	pula		    ; pull a from stack
	eora PIA1_PortB_DataDirection
	bita #0x0f	    ;  -00001111-
	beq  XmitRequestedRamLocation	 ; branch if equal (zero)
	bset *BitFlags_47, #b47_AisFail    ; set bits
XmitRequestedRamLocation:
	brclr *DRBSerialMode, #bbe_FastSerial, L1022	; branch if bit(s) clear
	ldaa CPU_SerialStatus	 ; load a with memory contents
	bita #0x0e	    ;  -00001110-
	beq  L1019	    ; branch if equal (zero)
	ldab CPU_SerialData	; load b with memory contents
	bra  L1022	    ; branch

L1019:	bita #0x20	    ;  -00100000-
	beq  L1022	    ; branch if equal (zero)
	ldab CPU_SerialData	; load b with memory contents
	cmpb #0xf2	    ;  -11110010- -0xf2 simply echos back 0xf2 as a confirmation of the logger mode
	beq  L1021	    ; branch if equal (zero)
	cmpb #0xfe	    ;  -11111110-  -0xfe kicks the serial port control back to the DRB routine
	bne  L1020	    ; branch if not equal (not zero)
	bclr *DRBSerialMode, #bbe_FastSerial | bbe_TestType3 | bbe_TestType2	; clear bits
L1020:	ldx  #0x0000	     ; load index with value
	abx		    ; add b to index
	ldab 0x00,x	    ; load b with memory at index + value
L1021:	stab CPU_SerialData	; store b into memory
L1022:	; jsr  HandleCCDBusComs	 ; call subroutine
L2022:	jsr  CheckIfMapSensorHasStartedWorkingAgain    ; call subroutine
	ldaa PIA2_PortB_ControlRegister    ; load a with memory contents
	eora #pia2b_OC1Toggle	       ; XOR a with value -00001000-
	staa PIA2_PortB_ControlRegister
	ldaa #0x80	    ; load a with value -10000000-
	sei		    ; disable interrupts
	oraa CPU_TimerInterruptMask1
	staa CPU_TimerInterruptMask1
	rti		    ; return from interrupt

HandleBaroReadRequirement_MM:
	brclr *BitFlags_54, #b54_FuelEngineNotRunning, EngRunning    ; branch if bit(s) clear
	bset *BitFlags_2d, #b2d_ReadBaroRequired    ; set bits
	rts		    ; return from subroutine

EngRunning:
	ldab BitFlags_51    ; load b with memory contents
	bmi  THROTTLE_PREVIOUSLY_NOTPRESSED    ; branch if minus(hi bit 1) b50_SparkEngineNotRunning
	ldaa Timer_BaroReadInterval    ; load a with memory contents
	tst  Counter_MainLoop
	bne  THROTTLE_PREVIOUSLY_NOTPRESSED    ; branch if not equal (not zero)
	inca		    ; increment a
	beq  THROTTLE_PREVIOUSLY_NOTPRESSED    ; branch if equal (zero)
	staa Timer_BaroReadInterval    ; store a into memory
THROTTLE_PREVIOUSLY_NOTPRESSED:
	ldaa BitFlags_4f    ; load a with memory contents
	bpl  ReadBaroIfPossible    ; branch if plus (hi bit 0) (Branch if b4f_OffIdle is set)
	bset *BitFlags_2d, #b2d_ReadBaroRequired    ; set bits
	clra		    ; a = 0
	staa Timer_BaroReadRpmConditionsSatisfied    ; store a into memory
	andb #~(b51_SparkEngineNotRunning | b51_BaroSolEnergized) 	 ;  -01011111-
	stab BitFlags_51    ; store b into memory
	bclr *BitFlags_54, #b54_BaroOkEngineStopped    ; clear bits
	rts		    ; return from subroutine

ReadBaroIfPossible:
	tstb		
	bmi  THROTTLE_HASNTCHANGED_STILLNOTPRESSED    ; branch if minus(hi bit 1)
	ldx  EngineRpm_HB
	cpx  BRPMHI_BaroReadHighRPM6650    ;  (data is bb80)
	bhi  R1028	    ; branch if higher
	cpx  BRPMLO_BaroReadLowRPM1800	  ;  (data is 3840)
	bcs  R1028	    ; branch if lower
	ldaa Timer_BaroReadRpmConditionsSatisfied    ; load a with memory contents
	inca		    ; increment a
	beq  L1023	    ; branch if equal (zero)
	staa Timer_BaroReadRpmConditionsSatisfied    ; store a into memory
	cmpa BRDLAY_BaroReadDelayAfterThrottleClosed2sec    ; compare a with memory contents (data is b6)
	bcs  R1028	    ; branch if lower
L1023:	ldaa Timer_BaroReadInterval    ; load a with memory contents
	cmpa BARTIM_BaroReadMinTimeBetweenReadings179sec    ; compare a with memory contents (data is 40)
	bcs  R1028	    ; branch if lower
	bitb #b51_BaroSolEnergized	    ;  -00100000-
	bne  R1028	    ; branch if not equal (not zero)
	bclr *BitFlags_2d, #b2d_ReadBaroRequired    ; clear bits
	ldab #b51_SparkEngineNotRunning	    ; load b with value -10000000-
	bra  L1024	    ; branch

THROTTLE_HASNTCHANGED_STILLNOTPRESSED:
	inc  Timer_BaroReadInterval
	bitb #b51_BaroSolEnergized	    ;  -00100000-
	bne  L1025	    ; branch if not equal (not zero)
	ldaa Timer_BaroReadInterval    ; load a with memory contents
	cmpa BROPTM_BaroReadDelayAfterSolenoidOpenTenthSec    ; compare a with memory contents (data is 09)
	bcs  R1028	    ; branch if lower
	ldab #b51_BaroSolEnergized	    ; load b with value -00100000-
	bset *BitFlags_54, #b54_BaroOkEngineStopped    ; set bits
L1024:	orab BitFlags_51
	bra  L1026	    ; branch

L1025:	brset *BitFlags_54, #b54_BaroOkEngineStopped, L1027    ; branch if bit(s) set
	bset *BitFlags_2d, #b2d_ReadBaroRequired    ; set bits
	ldaa Timer_BaroReadInterval    ; load a with memory contents
	cmpa BRCLTM_BaroReadDelayAfterSolenoidClosedTenthSec	; compare a with memory contents (data is 09)
	bcs  R1028	    ; branch if lower
	andb #~b51_SparkEngineNotRunning	  ;  -01111111-
L1026:	stab BitFlags_51    ; store b into memory
L1027:	clra		    ; a = 0
	staa Timer_BaroReadInterval    ; store a into memory
R1028:	rts		    ; return from subroutine

SaveBaroPressure:
; this routine stores the baro pressure, but it also returns with the scaled
; MAP value left in A...

	jsr  ConvertMAPVoltsToValue    ; call subroutine
	tab		    ; b = a
	cmpb BAROHI_BaroReadValidHighLimit    ; compare b with memory contents (data is 58)
	bcc  L1029	    ; branch if greater or equal
	cmpb BAROLO_BaroReadValidLowLimit    ; compare b with memory contents (data is 2e)
	bcc  L1030	    ; branch if greater or equal
L1029:	ldab BARDFT_BaroReadDefaultValue    ; load b with memory contents (data is 54)
L1030:	stab BaroPressure    ; store b into memory
	rts		    ; return from subroutine

        

ControlAsdRelay_MM:
	ldaa DRBPointer1    ; load a with memory contents
	cmpa #0x18	    ; compare a with value -00011000-
	bne  CONTROL_AUTOSHUTDOWN_RELAY_ROUTINE1    ; branch if not equal (not zero)
	ldaa DRBSerialMode    ; load a with memory contents
	bita #bbe_TestType3 | bbe_TestType2	     ;	-00110000-
	bne  CONTROL_AUTOSHUTDOWN_RELAY_ROUTINE1    ; branch if not equal (not zero)
	ldaa TimerOverflowsBetweenDistPulses	; load a with memory contents
	cmpa #0x28	    ; compare a with value -00101000-
	bls  L1032	    ; branch if lower or same
	ldaa DRBPointer2    ; load a with memory contents
	tab		    ; b = a
	anda #0x0f	    ; AND a with value -00001111-
	pshb		    ; push b onto stack
	lsrb		    ; logical shift right b
	lsrb		    ; logical shift right b
	lsrb		    ; logical shift right b
	lsrb		    ; logical shift right b
	comb		
	andb #0x0f	    ;  -00001111-
	cba		
	pulb		    ; pull b from stack
	bne  L1032	    ; branch if not equal (not zero)
	tst  Counter_MainLoop
	bne  L1031	    ; branch if not equal (not zero)
	deca		    ; decrement a
	beq  L1033	    ; branch if equal (zero)
	andb #0xf0	    ;  -11110000-
	addb #0x10	    ;  -00010000-
	aba		    ; a=a+b
	staa DRBPointer2    ; store a into memory
L1031:	ldaa #0xe1	    ; load a with value -11100001-
	jsr  SerialOutput1a    ; call subroutine
	ldx  #0xfe00	    ; load index with value
	bra  ASD_ToggleOnOff	    ; branch

L1032:	jsr  SerialOutput1    ; call subroutine
L1033:	clra		    ; a = 0
	staa DRBPointer1    ; store a into memory
CONTROL_AUTOSHUTDOWN_RELAY_ROUTINE1:
	ldx  #0x002d        ; load index with value
	ldaa CoolantTemp    ; load a with memory contents
	cmpa #0x8f	    ; compare a with value -10001111-
	bcc  ControlAsdRelay_Over119Ftemp    ; branch if greater or equal
	ldx  #0x005b        ; load index with value
ControlAsdRelay_Over119Ftemp:
	ldab #0x04	    ; load b with value -00000100-
	ldaa BatteryVolts   ; load a with memory contents
	cmpa #0xb2	    ; compare a with value -10110010-
	brset *BitFlags_51, #b51_Past12secRunning, ASD_EngRunningCheckBatVolts	; branch if bit(s) set
	bcc  ASD_ToggleOnOff ; branch if greater or equal
	cpx  #0x005b        ;  -00000000 01011011-
	bne  ASD_ToggleOnOff ; branch if not equal (not zero)
	ldab #0x0b	    ; load b with value -00001011-
	bra  ASD_ToggleOnOff ; branch

ASD_EngRunningCheckBatVolts:
	bcs  ASD_ToggleOnOff ; branch if bat volts is lower than 0xb2 (~11.3v)
	ldab #0x02	    ; load b with value -00000010-
ASD_ToggleOnOff:
	ldaa PIA1_A_Buffer  ; load a with memory contents
	anda #~pia1abuf_ASDRelay	  ; AND a with value -11011111- (set bits to turn ASD off)
	cmpb Counter_TimerPastHalfwayBetweenDistPulses ;0x02, 0x04, or 0x0b (11)
	bhi  ASD_StoreStateToBuffer	    ; branch if higher
	cpx  KeyOnOrEngineRunningTime       ; 0x002d or 0x005b
	bhi  ASD_StoreStateToBuffer	    ; branch if higher
	oraa #pia1abuf_ASDRelay 	 ;  -00100000- (set bits to turn ASD on)
ASD_StoreStateToBuffer:
	staa PIA1_A_Buffer    ; store a into memory
	brset *BitFlags_54, #b54_FuelEngineNotRunning, R1037	; branch if bit(s) set
	ldab KeyOnOrEngineRunningTime	 ; load b with memory contents
	cmpb #0x04	    ;  -00000100-
	bcs  R1037	    ; branch if lower
	bset *BitFlags_51, #b51_Past12secRunning	; set bits
R1037:	rts		    ; return from subroutine

ControlAirConditioning_MM:
	ldx  EngineRpm_HB
	ldaa PIA1_A_Buffer    ; load a with memory contents
	brset *BitFlags_2e, #b2e_bit2, SHUTOFF_AIRCONDITIONING	  ; branch if bit(s) set
	ldab TpsVolts	    ; load b with memory contents
	bita #pia1abuf_ACRelay		;  -00001000-
	beq  AIRCONDITIONING_CURRENTLY_OFF    ; branch if equal (zero)
	addb #0x03	    ;  -00000011-
AIRCONDITIONING_CURRENTLY_OFF:
	anda #~pia1abuf_ACRelay	    ; AND a with value -11110111-
	subb MINTHR_LowestSessionTPS	; b = b-memory contents
	bcs  L1038	    ; branch if lower
	cmpb ACOUT_DeltaAboveMinThrottleToCutOutAc    ; compare b with memory contents (data is 85)
	bcc  SHUTOFF_AIRCONDITIONING	; branch if greater or equal
L1038:	cpx  ACCRPM_DoNotAllowAcToEngageAboveThisRPM_4000    ;	(data is 7d00)
	bhi  R1040	    ; branch if higher
	cpx  TargetIdleSpeed_HB
	bcc  L1039	    ; branch if greater or equal
	cpx  ACLRPM_DisableAcBelowThisRPM_500	 ;  (data is 0fa0)
	bcc  R1040	    ; branch if greater or equal
SHUTOFF_AIRCONDITIONING:
	oraa #pia1abuf_ACRelay		;  -00001000-
L1039:	brset *BitFlags_51, #b51_SparkEngineNotRunning, R1040	 ; branch if bit(s) set
	staa PIA1_A_Buffer    ; store a into memory
R1040:	rts		    ; return from subroutine

DetermineTargetBatteryVoltage_MM:
	ldaa AmbientAirTempVolts    ; load a with memory contents
	cmpa AMBLOW_BattTempLowWhenHot	  ; compare a with memory contents (data is 05)
	bcs  AmbientTempSensorFault    ; branch if lower
	cmpa AMBHIG_BattTempHighWhenCold    ; compare a with memory contents (data is fa)
	bls  AmbientTempSensorValid    ; branch if lower or same

AmbientTempSensorFault:
	ldaa Counter_MainLoop	  ; load a with memory contents
	bita #0x7f	    ;  -01111111-
	bne  L1045	    ; branch if not equal (not zero)
	ldd  #0x0208	    ; load d (a&b) with value -00000010 00001000-
	jsr  ThrowNonCriticalError    ; call subroutine
	ldaa #0xe8	    ; load a with value -11100011-
	bra  L1042	    ; branch

AmbientTempSensorValid:
	ldab CPU_EEPROMControlReg    ; load b with memory contents
	bne  L1045	    ; branch if not equal (not zero)
	ldab #0x20	    ; load b with value -00100000-
	mul		    ; multiply (d=a*b)
	adca #0xd1	    ;  -11010001-
	cmpa #0xec	    ; compare a with value -11101100-
	bcs  L1041	    ; branch if lower
	ldaa #0xec	    ; load a with value -11101100-
L1041:	cmpa #0xd8	    ; compare a with value -11011000-
	bcc  L1042	    ; branch if greater or equal
	ldaa #0xd8	    ; load a with value -11011000-
L1042:	staa Temp0	    ; store a into memory
	ldab LB7E1	    ; load b with memory contents (data is ff)
	comb		
	cmpb CCDBTV_CCDBatteryVoltsOutput    ; compare b with memory contents (data is ff)
	bne  L1044	    ; branch if not equal (not zero)
	addb #0xf8	    ;  -11111000-
	bcs  L1043	    ; branch if lower
	mul		    ; multiply (d=a*b)
	adca #0x00	    ;  -00000000-
	bra  L1044	    ; branch

L1043:	cmpb #0x08	    ;  -00001000-
	bhi  L1044	    ; branch if higher
	mul		    ; multiply (d=a*b)
	adca Temp0	
	bcc  L1044	    ; branch if greater or equal
	ldaa #0xff	    ; load a with value -11111111-
L1044:	staa TargetBatteryVolts    ; store a into memory
L1045:	rts		    ; return from subroutine

ControlFan_MM:
	brclr *BitFlags_54, #b54_FuelEngineNotRunning, PreventRadSteaming    ; branch if bit(s) clear
	jmp  TurnFanOffByTimer

PreventRadSteaming:
	ldab PIA1_A_Buffer    ; load b with memory contents
	ldaa Timer_RadSteamingCountdown    ; load a with memory contents
	beq  L1048	    ; branch if equal (zero)
	ldaa CoolantTemp    ; load a with memory contents
	cmpa #0xd2	    ; compare a with value -11010010-
	bcs  L1048	    ; branch if lower
	ldaa Counter_MainLoop	  ; load a with memory contents
	cmpa #0x09	    ; compare a with value -00001001-
	bne  L1046	    ; branch if not equal (not zero)
	dec  Timer_RadSteamingCountdown    ; decrement memory contents
L1046:	clra		    ; a = 0
	bitb #pia1abuf_FanRelay 	 ;  -00010000-
	bne  L1047	    ; branch if not equal (not zero)
	inca		    ; increment a
L1047:	cmpa VehicleSpeed_HB	; compare a with memory contents
	bcc  TurnFanOn	    ; branch if greater or equal
L1048:	brset *b45_IPL1, #b45_BadCoolantTemp, TurnFanOn    ; branch if bit(s) set
	ldx  #FANTMP_FanTurnOnTempAbove45Mph	    ; load index with value
	ldaa VehicleSpeed_HB	; load a with memory contents
	cmpa FNSPHI_FanControlSpeedHi	    ; compare a with value 0x0b
	bcc  Below44MPH     ; branch if greater or equal
	cmpa FNSPLO_FanControlSpeedLo	    ; compare a with value 0x09
	bcs  Above36MPH     ; branch if lower
	brset *BitFlags_51, #b51_SpeedUnder40, L1049    ; branch if bit(s) set
Above36MPH:
	inx		    ; increment index (x=x+1)
	inx		    ; increment index (x=x+1)
	bclr *BitFlags_51, #b51_SpeedUnder40    ; clear bits
	bra  L1049	    ; branch

Below44MPH:
	bset *BitFlags_51, #b51_SpeedUnder40    ; set bits
L1049:	ldaa CONFIG_ConfigurationFlags	  ; load a with memory contents (data is 02)
	bita #cfg_AC		;  -10000000-
	beq  L1050	    ; branch if equal (zero)
	brset *BitFlags_54, #b54_FuelEngineNotRunning, L1050	; branch if bit(s) set
	bitb #pia1abuf_ACRelay	    ;  -00001000-
	beq  TurnFanOn	    ; branch if equal (zero)
L1050:	bitb #pia1abuf_FanRelay	    ;  -00010000-
	bne  L1051	    ; branch if not equal (not zero)
	inx		    ; increment index (x=x+1)
L1051:	ldaa 0x00,x	    ; load a with memory at index + value
	cmpa CoolantTemp    ; compare a with memory contents
	bcs  TurnFanOn	    ; branch if coolant temp is higher than setpoint
	ldaa BaroPressure    ; load a with memory contents
	adda FANMAP_FanTurnsOnWhenMapAboveBaroPlusThis	  ;  (data is ff)
	bcs  TurnFanOffByTimer	  ; branch if lower
	bitb #pia1abuf_FanRelay	    ;  -00010000-
	beq  CheckFor_FANMAP	; branch if equal (zero)
	adda #0x02	    ;  -00000010-
	bcs  TurnFanOffByTimer	  ; branch if lower
CheckFor_FANMAP:
	cmpa MapValue	    ; compare a with memory contents
	bcc  TurnFanOffByTimer	  ; branch if greater or equal
	ldaa AmbientAirTempVolts    ; load a with memory contents
	cmpa AMBLOW_BattTempLowWhenHot	  ; compare a with memory contents (data is 05)
	bcs  TurnFanOffByTimer	  ; branch if lower
	bitb #pia1abuf_FanRelay	    ;  -00010000-
	bne  L1052	    ; branch if not equal (not zero)
	deca		    ; decrement a
	deca		    ; decrement a
L1052:	cmpa FANBAT_FanTurnsOnWhenBatteryTempAboveThis	  ; compare a with memory contents (data is 1b)
	bcc  TurnFanOffByTimer	  ; branch if greater or equal
TurnFanOn:
	brset *BitFlags_51, #b51_SparkEngineNotRunning, R1056	 ; branch if bit(s) set
	brclr *PIA1_A_Buffer, #pia1abuf_FanRelay, R1056    ; branch if bit(s) clear
	andb #0xef	    ;  -11101111-
	ldaa #0x5b	    ; load a with value -01011011-
	staa Timer_MinimumFanRun    ; store a into memory
	ldaa AISFAN_AisKickWhenFanTurnsOnClosedThrottle    ; load a with memory contents (data is 03)
	beq  L1055	    ; branch if equal (zero)
	adda DesiredNewAisPosition
	bcs  L1053	    ; branch if lower
	cmpa AISHLM_AisHighLimitMaxOpenSteps	; compare a with memory contents (data is a0)
	bls  L1054	    ; branch if lower or same
L1053:	ldaa AISHLM_AisHighLimitMaxOpenSteps	; load a with memory contents (data is a0)
L1054:	staa DesiredNewAisPosition    ; store a into memory
	clra		    ; a = 0
	staa Timer_AisChanges	 ; store a into memory
	bra  L1055	    ; branch

TurnFanOffByTimer:
	ldaa Timer_MinimumFanRun    ; load a with memory contents
	beq  TurnFanOff     ; branch if equal (zero)
	deca		    ; decrement a
	staa Timer_MinimumFanRun    ; store a into memory
	rts		    ; return from subroutine

TurnFanOff:
	ldab PIA1_A_Buffer    ; load b with memory contents
	orab #pia1abuf_FanRelay 	 ;  -00010000-
	brset *BitFlags_51, #b51_SparkEngineNotRunning, R1056	 ; branch if bit(s) set
L1055:	stab PIA1_A_Buffer    ; store b into memory
R1056:	rts		    ; return from subroutine

ControlPurgeSolenoid_MM:
	brclr *BitFlags_54, #b54_FuelEngineNotRunning, L1058	; branch if bit(s) clear
	ldaa CoolantTemp    ; load a with memory contents
	cmpa PURTMP_CanisterPurgeCoolantTemp	    ; compare a with memory contents (data is 82)
	bcc  L1057	    ; branch if greater or equal
	bclr *BitFlags_50, #b50_Purge	 ; clear bits
	bra  L1058	    ; branch

L1057:	bset *BitFlags_50, #b50_Purge	 ; set bits
L1058:	brclr *BitFlags_4f, #b4f_PTEisMaxed | b4f_FullThrottle, L1059	 ; branch if bit(s) clear
CanisterPurgeOff:
	bclr *PIA1_A_Buffer, #pia1abuf_PurgeSolenoid	; clear bits
	rts		    ; return from subroutine

L1059:	ldab BaroPressure    ; load b with memory contents
	brset *PIA1_A_Buffer, #pia1abuf_PurgeSolenoid, L1060	; branch if bit(s) set
	subb PURHYS_CannisterPurgeBaroHysteresis    ; subtract memory contents from b (data is 01)
L1060:	subb PURMAP_CannisterPurgeWhenBelowThisBaro    ; subtract memory contents from b (data is 03)
	cmpb MapValue	
	bcs  CanisterPurgeOff	 ; branch if lower
	brset *BitFlags_50, #b50_Purge, CanisterPurgeOn    ; branch if bit(s) set
	brset *BitFlags_50, #b50_OpenLoop, CanisterPurgeOff    ; branch if bit(s) set
	bset *BitFlags_50, #b50_Purge	 ; set bits
	bra  L1061	    ; branch

CanisterPurgeOn:
	brset *BitFlags_4f, #b4f_O2Valid, L1061    ; branch if bit(s) set
	ldab Timer_CLTIME_ClosedLoopTimer    ; load b with memory contents
	bne  CanisterPurgeOff	 ; branch if not equal (not zero)
L1061:	ldaa BitFlags_2e    ; load a with memory contents
	anda #b2e_BadO2Read		; AND a with value -00000011-
	cmpa #b2e_BadO2Read		; compare a with value -00000011-
	bne  SET_BITS_TO_TURN_ON_CANISTER_PURGING    ; branch if not equal (not zero)
	ldaa Counter_AdaptiveMem_Erase	  ; load a with memory contents
	cmpa #0x15	    ; compare a with value -00010101-
	bcs  SET_BITS_TO_TURN_ON_CANISTER_PURGING    ; branch if lower
	cmpa #0x1e	    ; compare a with value -00011110-
	bhi  SET_BITS_TO_TURN_ON_CANISTER_PURGING    ; branch if higher
	brclr *BitFlags_4f, #b4f_O2Rich, SET_BITS_TO_TURN_ON_CANISTER_PURGING	 ; branch if bit(s) clear
	brset *BitFlags_53, #b53_PurgeSolenoid, CanisterPurgeOff    ; branch if bit(s) set
	brset *BitFlags_4f, #b4f_OffIdle, SET_BITS_TO_TURN_ON_CANISTER_PURGING	  ; branch if bit(s) set
	bset *BitFlags_53, #b53_PurgeSolenoid	 ; set bits
	brclr *PIA1_A_Buffer, #pia1abuf_PurgeSolenoid, CanisterPurgeOff    ; branch if bit(s) clear
	clra		    ; a = 0
	staa Counter_PrimaryAndSecondaryRamp    ; store a into memory
	bra  CanisterPurgeOff	 ; branch

SET_BITS_TO_TURN_ON_CANISTER_PURGING:
	bclr *BitFlags_53, #b53_PurgeSolenoid	 ; clear bits
	bset *PIA1_A_Buffer, #pia1abuf_PurgeSolenoid	; set bits
	rts		    ; return from subroutine

CalculateAisPosition_MM:
	ldaa BitFlags_54    ; load a with memory contents
	oraa BitFlags_AIS    ; OR a with memory contents
	oraa BitFlags_4f    ; OR a with memory contents
	bmi  R1062	    ; branch if minus(hi bit 1) - Engine Not Running, Off Idle, And somethign else?
	brset *BitFlags_50, #b50_IdleSpeedMode, R1062	 ; branch if bit(s) set
	ldaa b45_IPL1    ; load a with memory contents
	anda #b45_MapStuck | b45_MapBadSignal	       ; AND a with value -10100000-
	oraa TimerOverflowsBetweenDistPulses	; OR a with memory contents
	oraa Timer_CountdownFromStartRunForAisFeedback	  ; OR a with memory contents
	beq  L1063	    ; branch if equal (zero)
R1062:	rts		    ; return from subroutine

L1063:	ldaa Timer_DacalCountdown	    ; load a with memory contents
	lsra		
	lsra		
	adda DANOM_Base_nominalCal    ;  (data is 12)
	bcs  L1064	    ; branch if lower
	brclr *BitFlags_50, #b50_FallToIdle, L1065    ; branch if bit(s) clear
	staa Temp0	    ; store a into memory
	ldx  #TIMEDC_AISDecelBaseAirflowCurveOffset    ; load index with value
	ldaa KeyOnOrEngineRunningTime	 ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	adda Temp0	
	bcs  L1064	    ; branch if lower
	staa Temp0	    ; store a into memory
	ldx  #TEMPDC_AISDecel_FromTemp	 ; load index with value
	ldaa CoolantTemp    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	adda Temp0	
	bcs  L1064	    ; branch if lower
	brset *StartupSwitchMirror2, #sw2_ACclutch, L1065    ; branch if bit(s) set
	adda DAACF_ACFactorDeltaFromBase    ;  (data is 12)
	bcc  L1065	    ; branch if greater or equal
L1064:	ldaa #0xff	    ; load a with value -11111111-
L1065:	ldab DistributorFallingEdgePulsewidth_HB    ; load b with memory contents
	mul		    ; multiply (d=a*b)
	asld		    ; shift left (d=d*2)
	bcs  L1066	    ; branch if lower
	asld		    ; shift left (d=d*2)
	bcs  L1066	    ; branch if lower
	asld		    ; shift left (d=d*2)
	bcs  L1066	    ; branch if lower
	staa Temp0	    ; store a into memory
	ldx  #MAPFLR_AISAdditionToControlMap_FromRpm	; load index with value
	ldaa EngineRpm_HB    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Temp1	    ; store a into memory
	ldx  #MPTEMP_TempTermForMapOffset_FromTemp	; load index with value
	ldaa CoolantTemp    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	ldaa Temp1	    ; load a with memory contents
	mul		    ; multiply (d=a*b)
	adca Temp0	
	bcs  L1066	    ; branch if lower
	staa Temp0	    ; store a into memory
	ldx  #BARFLR_OffsetCorrectionTo_MAPFLR_FromBaro	  ; load index with value
	ldaa BaroPressure    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	adda Temp0	
	bcc  L1067	    ; branch if greater or equal
L1066:	ldaa #0xff	    ; load a with value -11111111-
L1067:	brset *BitFlags_50, #b50_FallToIdle, L1076    ; branch if bit(s) set
	ldab CONFIG_ConfigurationFlags	  ; load b with memory contents (data is 02)
	bitb #cfg_ATX		;  -00100000-
	beq  L1068	    ; branch if equal (zero)
	brclr *StartupSwitchMirror2, #sw2_PNswitch, R1075	 ; branch if bit(s) clear
L1068:	ldab KeyOnOrEngineRunningTime	 ; load b with memory contents
	cmpb DCALTM_DacalInhibitTimeAfterStartup    ; compare b with memory contents (data is 19)
	bcs  R1075	    ; branch if lower
	brclr *StartupSwitchMirror2, #sw2_ACclutch, R1075    ; branch if bit(s) clear
	ldab CoolantTemp    ; load b with memory contents
	cmpb DATHOT_EngineTempToStartCalibratingDacal	 ; compare b with memory contents (data is cd)
	bls  R1075	    ; branch if lower or same
	ldab Counter_MainLoop	  ; load b with memory contents
	bitb DCALRT_DacalUpdateRate01_03_07_0f_1f_3f_7f_ff    ;  (data is 7f)
	bne  L1072	    ; branch if not equal (not zero)
	ldab TargetIdleSpeed_HB	; load b with memory contents
	subb EngineRpm_HB    ; b = b-memory contents
	bcc  L1069	    ; branch if greater or equal
	negb		
L1069:	cmpb DADRPM_DeltaRpmFromIdleSpeedForDacalUpdate    ; compare b with memory contents (data is 04)
	bhi  L1072	    ; branch if higher
	ldab Timer_DacalCountdown	    ; load b with memory contents
	cmpa MapValue	    ; compare a with memory contents
	bhi  L1070	    ; branch if higher
	incb		
	bne  L1071	    ; branch if not equal (not zero)
L1070:	tstb
	beq  L1072	    ; branch if equal (zero)
	decb		
L1071:	stab Timer_DacalCountdown	    ; store b into memory
L1072:	ldab Counter_MainLoop	  ; load b with memory contents
	bitb CALRAT_AisAdjustRate    ;	(data is 07)
	bne  R1075	    ; branch if not equal (not zero)
	ldd  EngineRpm_HB    ; load d (a&b) with memory contents
	subd TargetIdleSpeed_HB	; d = d - memory contents
	bcc  L1073	    ; branch if greater or equal
	coma		
	comb		
	addd #0x0001	     ;	-00000000 00000001-
L1073:	asld		    ; shift left (d=d*2)
	bcs  R1075	    ; branch if lower
	asld		    ; shift left (d=d*2)
	bcs  R1075	    ; branch if lower
	cmpa #0x0a	    ; compare a with value -00001010-
	bcc  R1075	    ; branch if greater or equal
	ldaa DesiredNewAisPosition    ; load a with memory contents
	cmpa CurrentAisPosition    ; compare a with memory contents
	bne  R1075	    ; branch if not equal (not zero)
	cmpa CALPOS_PositionAisMotorIsAtIdle	; compare a with memory contents (data is 1a)
	beq  R1075	    ; branch if equal (zero)
	bhi  L1074	    ; branch if higher
	inca		    ; increment a
	inca		    ; increment a
L1074:	deca		    ; decrement a
	staa DesiredNewAisPosition    ; store a into memory
	staa CurrentAisPosition    ; store a into memory
R1075:	rts		    ; return from subroutine

L1076:	ldab Timer_AisChanges	 ; load b with memory contents
	cmpb DCLRFQ_TimeBetweenAisPulsesForDecelAis    ; compare b with memory contents (data is 3f)
	bcs  R1075	    ; branch if lower
	cmpa DCLMIN_MinLimitOnDecelAisControlledMap    ; compare a with memory contents (data is 0a)
	bcc  L1077	    ; branch if greater or equal
	ldaa DCLMIN_MinLimitOnDecelAisControlledMap    ; load a with memory contents (data is 0a)
L1077:	cmpa DCLMN2_NoAisControlIfMapAndControlMapBelowThis    ; compare a with memory contents (data is 0d)
	bcc  L1078	    ; branch if greater or equal
	ldab MapValue	    ; load b with memory contents
	cmpb DCLMN2_NoAisControlIfMapAndControlMapBelowThis    ; compare b with memory contents (data is 0d)
	bcs  R1075	    ; branch if lower
L1078:	ldx  #DAISOP_DecelAisOpenStepsFromNeg_FromDeltaMap    ; load index with value
	suba MapValue	
	bcc  L1079	    ; branch if greater or equal
	nega		    ; negate a (set high bit)
	ldx  #DAISCL_DecelAisOpenStepsFromPos_FromDeltaMap    ; load index with value
L1079:	jsr  Lookup4ByteTable	 ; call subroutine
	jsr  StoreAndLimitDesiredAisPosition	; call subroutine
	cmpa CurrentAisPosition    ; compare a with memory contents
	beq  R1075	    ; branch if equal (zero)
	clra		    ; a = 0
	staa Timer_AisChanges	 ; store a into memory
	rts		    ; return from subroutine

KickUpAisBy2DuringDecel_MM:
	ldab Counter_MainLoop	  ; load b with memory contents
	bitb #0x7f	    ;  -01111111-
	bne  R1080	    ; branch if not equal (not zero)
	brset *BitFlags_50, #b50_FallToIdle, R1080    ; branch if bit(s) set
	brset *b45_IPL1, #b45_MapStuck, R1080    ; branch if bit(s) set
	brset *b45_IPL1, #b45_MapBadSignal, R1080	; branch if bit(s) set
	ldaa DesiredNewAisPosition    ; load a with memory contents
	oraa CurrentAisPosition    ; OR a with memory contents
	bne  R1080	    ; branch if not equal (not zero)
	adda #0x02	    ;  -00000010-
	staa DesiredNewAisPosition    ; store a into memory
	staa CurrentAisPosition    ; store a into memory
	bset *BitFlags_51, #b51_bit6	; set bits
R1080:	rts		    ; return from subroutine

CalculateTargetIdleSpeedAndAisPosition_MM:
	ldaa ATMOffset	    ; load a with memory contents
	cmpa #0x07	    ; compare a with value -00000111-
	beq  R1081	    ; branch if equal (zero)
	cmpa #0x14	    ; compare a with value -00010100-
	bne  L96B6	    ; branch if not equal (not zero)
R1081:	rts		    ; return from subroutine

; this is the start of the decel fuel cut code...

; need to check all of these values
L96B6:  brset *BitFlags_AIS, #b0c_ATXInGear, L1082    ; branch if bit(s) set
        brset *BitFlags_54, #b54_FuelEngineNotRunning, ClearDFCFlag    ; branch if bit(s) set
        ldaa KeyOnOrEngineRunningTime    ; load a with memory contents
        cmpa DCLMER_MinTimeEngineRunningForDecelFuelShutoff    ; compare a with memory contents (data is 02)
        bls  ClearDFCFlag          ; branch if lower or same
        ldaa CoolantTemp    ; load a with memory contents
        cmpa DCLMCT_MinCoolantTempForDecelFuelShutoff    ; compare a with memory contents (data is d2)
        bls  ClearDFCFlag          ; branch if lower or same
        brset *BitFlags_4f, #b4f_OffIdle, ClearDFCFlag    ; branch if bit(s) set
        ldd  VehicleSpeed_HB    ; load d (a&b) with memory contents
        asld                ; shift left (d=d*2)
        asld                ; shift left (d=d*2)
        asld                ; shift left (d=d*2)
        lslb
        adca #0x00          ;  -00000000-
        cmpa MPHREF_SwitchPointForDecelIdleAisControl    ; compare a with memory contents (data is 07)
        bcc  ClearDFCFlag          ; branch if greater or equal
        ldd  EngineRpm_HB    ; load d (a&b) with memory contents
        subd TargetIdleSpeed_HB    ; d = d - memory contents
        bcc  L96E4          ; branch if greater or equal
        clra                ; a = 0
L96E4:  brclr *Turbonator_Flags, #Turbonator_DecelFuelCut, L96F8    ; branch if bit(s) clear
        cmpa DCLRPL_EngineRPMLimitForDecelFuelShutoffLow    ; compare a with memory contents (data is 0f)
        bhi  SetDFCFlag          ; branch if higher
        ldaa DCAISI_AISIncrementWhenUsingDecelFuelShut    ; load a with memory contents (data is 00)
        jsr  ClearAisTimer    ; call subroutine

ClearDFCFlag:
        bclr *Turbonator_Flags, #Turbonator_DecelFuelCut    ; clear bits
        bra  L1082          ; branch

L96F8:  cmpa DCLRPH_EngineRPMLimitForDecelFuelShutoffHigh    ; compare a with memory contents (data is 11)
        bls  ClearDFCFlag          ; branch if lower or same

SetDFCFlag:
        bset *Turbonator_Flags, #Turbonator_DecelFuelCut    ; set bits
        clr  Timer_CountdownFromStartRunForAisFeedback    ; zero byte at memory location
; this is the end of the main pportion of the decel fuel cut code...


L1082:	ldaa BaroPressure    ; load a with memory contents
	ldx  #BARAIS_AISBaroCompensation    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Temp1	    ; store a into memory
	ldaa DRBPointer1    ; load a with memory contents
	cmpa #0x14	    ; compare a with value -00010100-
	bne  L1083	    ; branch if not equal (not zero)
	ldaa DRBPointer2    ; load a with memory contents
	cmpa #0x10	    ; compare a with value -00010000-
	bne  L1083	    ; branch if not equal (not zero)
LoadDiagIdleSpeed:
	ldaa #0x30	    ; load a with value -00110000-
	bra  L1089	    ; branch

L1083:	brset *BitFlags_AIS, #b0c_ATXChngGear, L1092	; branch if bit(s) set
	ldx  #AISCLD_IdleSpeedDrive_FromTemp	  ; load index with value
	brset *BitFlags_AIS, #b0c_ATXInGear, L1086    ; branch if bit(s) set
	ldaa DRBPointer1    ; load a with memory contents
	cmpa #0x19	    ; compare a with value -00011001-
	beq  L1084	    ; branch if equal (zero)
	brclr *BitFlags_50, #b50_InMotion, L1085    ; branch if bit(s) clear
	ldd  TargetIdleSpeed_HB	; load d (a&b) with memory contents
	subd #0x0001	     ;	-00000000 00000001-
	bitb #0x3f	    ;  -00111111-
	bne  L1091	    ; branch if not equal (not zero)
	bclr *BitFlags_50, #b50_InMotion    ; clear bits
	bra  L1091	    ; branch

L1084:	brset *DRBSerialMode, #bbe_TestType3, L1092    ; branch if bit(s) set
	clr  DRBPointer1    ; zero byte at memory location
	ldaa DRBPointer2    ; load a with memory contents
	ldab #0xff	    ; load b with value -11111111-
	bset *BitFlags_50, #b50_InMotion    ; set bits
	bra  L1090	    ; branch

L1085:	ldaa IDLDEF_TargetIdleSpeed_HBDefault    ; load a with memory contents (data is 7d)
	brset *b45_IPL1, #b45_BadCoolantTemp, L1089	  ; branch if bit(s) set
	ldx  #AISPN_IdleSpeedParkNeutral_FromTemp	; load index with value
L1086:	ldaa CoolantTemp    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Temp0	    ; store a into memory
	ldaa KeyOnOrEngineRunningTime	 ; load a with memory contents
	ldx  #TIMED2_AISDecelBaseAirflowCurveOffset2	; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	adda Temp0	
	bcc  L1087	    ; branch if greater or equal
	ldaa #0xff	    ; load a with value -11111111-
L1087:	brclr *BitFlags_50, #b50_IdleSpeedMode, L1089	 ; branch if bit(s) clear
	ldab Counter_MainLoop	  ; load b with memory contents
	andb DECAIS_RollingAisUpdateRate_01_03_07_0f_1f_3f_7f_ff    ;  (data is 7f)
	bne  L1092	    ; branch if not equal (not zero)
	staa Temp0	    ; store a into memory
	ldd  TargetIdleSpeed_HB	; load d (a&b) with memory contents
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	suba ISPDCY_RollingAisDecay    ;  (data is 04)
	bcs  L1088	    ; branch if lower
	cmpa Temp0	    ; compare a with memory contents
	bcc  L1089	    ; branch if greater or equal
L1088:	ldaa Temp0	    ; load a with memory contents
L1089:	clrb		    ; b = 0
L1090:	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
L1091:	stD *TargetIdleSpeed_HB	; store D to RAM
L1092:	brset *BitFlags_AIS, #b0c_bit6, L1094	 ; branch if bit(s) set
	brclr *BitFlags_54, #b54_FuelEngineNotRunning, L1093	; branch if bit(s) clear
	ldaa EngineRpm_HB    ; load a with memory contents
	cmpa RPMTHS_RPMThresholdForIdleControl	  ; compare a with memory contents (data is 19)
	bcc  L1093	    ; branch if greater or equal
	ldaa RPMDEF_RPMDefaultForIdleControl	; load a with memory contents (data is a0)
	jmp  L1149	

L1093:	bset *BitFlags_AIS, #b0c_bit6	 ; set bits
	bra  L1095	    ; branch

L1094:	ldab BitFlags_AIS    ; load b with memory contents
	orab BitFlags_54
	bpl  L1096	    ; branch if plus (hi bit 0)
	ldaa DesiredNewAisPosition    ; load a with memory contents
	cmpa CurrentAisPosition    ; compare a with memory contents
	bne  L1095	    ; branch if not equal (not zero)
	brset *BitFlags_AIS, #b0c_UseAIS, L1095    ; branch if bit(s) set
	bclr *BitFlags_AIS, #b0c_bit7	 ; clear bits
L1095:	bset *BitFlags_AIS, #b0c_bit4	 ; set bits
	bset *BitFlags_2e, #b2e_bit2	; set bits
	ldaa CoolantTemp    ; load a with memory contents
	ldx  #AISTRT_AisStartupPosition_FromTemp    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	jmp  L1149	

L1096:	brclr *b45_IPL1, #b45_MapStuck | b45_MapBadSignal, HandleAcCutout	; branch if bit(s) clear
	ldaa #0x20	    ; load a with value -00100000-
	staa DesiredNewAisPosition    ; store a into memory
	brclr *BitFlags_2e, #b2e_AcClutch, L1097    ; branch if bit(s) clear
	bset *BitFlags_2e, #b2e_bit2	; set bits
	rts		    ; return from subroutine

L1097:	bclr *BitFlags_2e, #b2e_bit2	; clear bits
	rts		    ; return from subroutine

HandleAcCutout:
	ldaa KeyOnOrEngineRunningTime	 ; load a with memory contents
	cmpa ACCTIM_AcDelayFromStartRunTransfer    ; compare a with memory contents (data is 04)
	bcs  L1103	    ; branch if lower
	ldaa Timer_AcCutout    ; load a with memory contents
	bne  L1098	    ; branch if not equal (not zero)
	ldaa CoolantTemp    ; load a with memory contents
	cmpa ACDTMP_PartThrottleAcCutoutDisableTemp    ; compare a with memory contents (data is ff)
	bcs  L1100	    ; branch if lower
	ldaa TpsVolts	    ; load a with memory contents
	suba MINTHR_LowestSessionTPS
	bcs  L1100	    ; branch if lower
	cmpa ACDTHR_PartThrottleAcCutoutDisableThrottle    ; compare a with memory contents (data is ff)
	bcs  L1100	    ; branch if lower
	ldx  VehicleSpeed_HB
	cpx  ACDSPD_PartThrottleAcCutoutDisableSpeed	;  (data is 0000)
	bcc  L1100	    ; branch if greater or equal
	inc  Timer_AcCutout
	brset *BitFlags_AIS, #b0c_bit4, L1103	 ; branch if bit(s) set
	jmp  L1113

L1098:	cmpa ACETIM_PartThrottleAcCutoutMaxTimeActive	 ; compare a with memory contents (data is 08)
	bcc  L1099	    ; branch if greater or equal
	ldx  VehicleSpeed_HB
	cpx  ACESPD_AllowAcClutchAboveThisSpeed    ;  (data is 0500)
	bcc  L1099	    ; branch if greater or equal
	ldab EngineRpm_HB    ; load b with memory contents
	cmpb ACERPM_AllowAcClutchAboveThisRpm	 ; compare b with memory contents (data is 44)
	bcc  L1099	    ; branch if greater or equal
	ldab Counter_MainLoop	  ; load b with memory contents
	bitb Counter_SomethingWithDistributor
	bne  L1103	    ; branch if not equal (not zero)
	inca		    ; increment a
	staa Timer_AcCutout    ; store a into memory
	bra  L1103	    ; branch

L1099:	clra		    ; a = 0
	staa Timer_AcCutout    ; store a into memory
L1100:	ldab BitFlags_AIS    ; load b with memory contents
	eorb BitFlags_2e
	andb #b2e_AcClutch	    ;  -00010000-
	beq  L1104	    ; branch if equal (zero)
	eorb BitFlags_AIS
	bitb #b0c_bit4		;  -00010000-
	beq  L1101	    ; branch if equal (zero)
	jmp  L1113	

L1101:	ldaa Pulsewidth_PartThrottleEnrichment_HB    ; load a with memory contents
	bne  L1102	    ; branch if not equal (not zero)
	ldaa Pulsewidth_PartThrottleEnrichment_LB    ; load a with memory contents
	beq  L1111	    ; branch if equal (zero)
L1102:	ldaa ACAETH_DisallowAcClutchEngageForThisTimeAfterAccelEnrich	 ; load a with memory contents (data is 2d)
	staa Timer_AcClutchEngageRestrictionTimer    ; store a into memory
L1103:	jmp  L1119

; looks like there should be a clrb here before storing the Timer_ ? That's how LB60 is, not sure why you'd want to store a flag value into a timer...
L1104:	stab Timer_AcClutchEngageRestrictionTimer    ; store b into memory
	brset *BitFlags_AIS, #b0c_bit4, L1107	 ; branch if bit(s) set
	ldaa Timer_AisOrO2Sensor    ; load a with memory contents
	bne  L1106	    ; branch if not equal (not zero)
L1105:	jmp  L1117

L1106:	clrb		    ; b = 0
	stab Timer_AisChanges	 ; store b into memory
	deca		    ; decrement a
	staa Timer_AisOrO2Sensor    ; store a into memory
	bne  L1103	    ; branch if not equal (not zero)
	brset *BitFlags_4f, #b4f_OffIdle, L1105    ; branch if bit(s) set
	ldaa AC2KCK_AcClutchKickOpenAfterAcEnabled    ; load a with memory contents (data is 04)
	jsr  MultiplyTempvar1ByA    ; call subroutine
	jsr  StoreAndLimitDesiredAisPosition	; call subroutine
	jmp  L1117	

L1107:	ldaa Timer_AisOrO2Sensor    ; load a with memory contents
	beq  L1103	    ; branch if equal (zero)
	clrb		    ; b = 0
	stab Timer_AisChanges	 ; store b into memory
	deca		    ; decrement a
	staa Timer_AisOrO2Sensor    ; store a into memory
	bne  L1105	    ; branch if not equal (not zero)
	brset *BitFlags_4f, #b4f_OffIdle, L1110    ; branch if bit(s) set
	ldaa MapValue	    ; load a with memory contents
	cmpa DCLMN2_NoAisControlIfMapAndControlMapBelowThis    ; compare a with memory contents (data is 0d)
	bls  L1108	    ; branch if lower or same
	ldaa AC3KCK_AcClutchKickOpenAfterAcEnabled2    ; load a with memory contents (data is fe)
	bra  L1109	    ; branch

L1108:	ldaa AC2KCK_AcClutchKickOpenAfterAcEnabled    ; load a with memory contents (data is 04)
	nega		    ; negate a (set high bit)
L1109:	jsr  L1157	    ; call subroutine
	jsr  StoreAndLimitDesiredAisPosition	; call subroutine
	bra  L1119	    ; branch

L1110:	ldx  #ACCTBL_ACOffIdleDelta_FromSpeed	 ; load index with value
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	jsr  Lookup4ByteTable	 ; call subroutine
	ldab OFFPER2_AisInstantlyClosesWhenAcDisengages2	  ; load b with memory contents (data is 40)
	mul		    ; multiply (d=a*b)
	jsr  MultiplyTempvar1ByA    ; call subroutine
	nega		    ; negate a (set high bit)
	jsr  L1162	    ; call subroutine
	bra  L1119	    ; branch

L1111:	ldaa Timer_AcClutchEngageRestrictionTimer    ; load a with memory contents
	beq  L1112	    ; branch if equal (zero)
	deca		    ; decrement a
	staa Timer_AcClutchEngageRestrictionTimer    ; store a into memory
	bne  L1119	    ; branch if not equal (not zero)
L1112:	stab BitFlags_AIS    ; store b into memory
	ldaa ACTIME_TimeBeforeAcEnabledAndFullDeltaUsed    ; load a with memory contents (data is 24)
	staa Timer_AisOrO2Sensor    ; store a into memory
	brset *BitFlags_4f, #b4f_OffIdle, L1118    ; branch if bit(s) set
	ldaa ACOFFK_ClosedThrottleAcOffKick    ; load a with memory contents (data is 08)
	jsr  MultiplyTempvar1ByA    ; call subroutine
	jsr  ClearAisTimer	    ; call subroutine
	bra  L1119	    ; branch

L1113:	bset *BitFlags_AIS, #b0c_bit4	 ; set bits
	ldaa ACTIM2_TimeBeforeAcEnabledAndFullDeltaUsed2    ; load a with memory contents (data is 24)
	staa Timer_AisOrO2Sensor    ; store a into memory
	brset *BitFlags_4f, #b4f_OffIdle, L1116    ; branch if bit(s) set
	ldaa MapValue	    ; load a with memory contents
	cmpa DCLMN2_NoAisControlIfMapAndControlMapBelowThis    ; compare a with memory contents (data is 0d)
	bls  L1114	    ; branch if lower or same
	ldaa AC4KCK_AcClutchKickOpenBeforeAcEnabled2	; load a with memory contents (data is fa)
	bra  L1115	    ; branch

L1114:	ldaa ACOFFK_ClosedThrottleAcOffKick    ; load a with memory contents (data is 08)
	nega		    ; negate a (set high bit)
L1115:	jsr  L1157	    ; call subroutine
	jsr  ClearAisTimer	    ; call subroutine
	bra  L1117	    ; branch

L1116:	ldx  #ACCTBL_ACOffIdleDelta_FromSpeed	 ; load index with value
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	jsr  Lookup4ByteTable	 ; call subroutine
	ldab OFFPER_AisInstantlyClosesWhenAcDisengages	  ; load b with memory contents (data is c0)
	mul		    ; multiply (d=a*b)
	jsr  MultiplyTempvar1ByA    ; call subroutine
	nega		    ; negate a (set high bit)
	jsr  L1162	    ; call subroutine
	clra		    ; a = 0
	staa Timer_AisChanges	 ; store a into memory
L1117:	bclr *BitFlags_2e, #b2e_bit2	; clear bits
	bra  L1120	    ; branch

L1118:	clra		    ; a = 0
	staa Timer_AisChanges	 ; store a into memory
L1119:	bset *BitFlags_2e, #b2e_bit2	; set bits
L1120:	brclr *BitFlags_4f, #b4f_OffIdle, L1121    ; branch if bit(s) clear
	bclr *BitFlags_AIS, #b0c_ATXChngGear	; clear bits
	brclr *StartupSwitchMirror2, #sw2_Brake, L1122	 ; branch if bit(s) clear
	ldx  #BRKRPM_BrakeOverrideForAis_FromDeltaThrottle    ; load index with value
	ldaa TpsVolts	    ; load a with memory contents
	suba MINTHR_LowestSessionTPS
	jsr  Lookup4ByteTable	 ; call subroutine
	cmpb EngineRpm_HB
	bcc  L1122	    ; branch if greater or equal
L1121:	brclr *BitFlags_2e, #b2e_AtIdle, L1123	  ; branch if bit(s) clear
L1122:	jmp  L1143

L1123:	brclr *BitFlags_50, #b50_FallToIdle, L1124    ; branch if bit(s) clear
	rts		    ; return from subroutine

L1124:	ldaa DesiredNewAisPosition    ; load a with memory contents
	cmpa #0x04	    ; compare a with value -00000100-
	bcs  L1125	    ; branch if lower
	bclr *BitFlags_51, #b51_bit6	; clear bits
L1125:	brclr *BitFlags_AIS, #b0c_ATXChngGear, L1130	; branch if bit(s) clear
	brclr *BitFlags_AIS, #b0c_ATXInGear, L1126    ; branch if bit(s) clear
	ldx  #PNDLTP_DeltaRpmChangeToUse_DRPNK_or_PNDRK    ; load index with value
	ldd  TargetIdleSpeed_HB	; load d (a&b) with memory contents
	subd EngineRpm_HB    ; d = d - memory contents
	bra  L1127	    ; branch

L1126:	ldx  #PNDLTN_DeltaRpmChangeToUse_DRPNK_or_PNDRK    ; load index with value
	ldd  EngineRpm_HB    ; load d (a&b) with memory contents
	subd TargetIdleSpeed_HB	; d = d - memory contents
L1127:	bcs  L1130	    ; branch if lower
	subd 0x00,x	
	bcs  L1130	    ; branch if lower
	ldaa CoolantTemp    ; load a with memory contents
	inx		    ; increment index (x=x+1)
	inx		    ; increment index (x=x+1)
	jsr  Lookup4ByteTable	 ; call subroutine
	bmi  L1128	    ; branch if minus(hi bit 1)
	jsr  MultiplyTempvar1ByA    ; call subroutine
	bra  L1129	    ; branch

L1128:	jsr  L1157	    ; call subroutine
L1129:	jsr  ClearAisTimer	    ; call subroutine
	bclr *BitFlags_AIS, #b0c_ATXChngGear	; clear bits
L1130:	ldaa Timer_CountdownFromStartRunForAisFeedback	  ; load a with memory contents
	bne  R1142	    ; branch if not equal (not zero)
	ldab AISFRQ_AisPeriodForRpmFeedback11ms    ; load b with memory contents (data is 7f)
	cmpb Timer_AisChanges
	bcc  L1136	    ; branch if greater or equal
	ldx  #FWDAIS_ForwardAisSteps_NoSlope	; load index with value
	ldd  TargetIdleSpeed_HB	; load d (a&b) with memory contents
	subd EngineRpm_HB    ; d = d - memory contents
	bcc  L1131	    ; branch if greater or equal
	ldx  #REVAIS_ReverseAisSteps_NoSlope	; load index with value
	coma		
	comb		
L1131:	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	brset *BitFlags_AIS, #b0c_ATXInGear, L1132    ; branch if bit(s) set
	lsrd		    ; shift right (d=d/2)
L1132:	tsta		    ; test a
	beq  L1133	    ; branch if equal (zero)
	ldab #0xff	    ; load b with value -11111111-
L1133:	tba		    ; a = b
	cmpa 0x01,x	    ; compare a with memory at index + value
	bcs  L1136	    ; branch if lower
	ldab 0x00,x	    ; load b with memory at index + value
	beq  L1136	    ; branch if equal (zero)
L1134:	inx		    ; increment index (x=x+1)
	inx		    ; increment index (x=x+1)
	decb		
	beq  L1135	    ; branch if equal (zero)
	cmpa 0x01,x	    ; compare a with memory at index + value
	bcc  L1134	    ; branch if greater or equal
L1135:	ldaa 0x00,x	    ; load a with memory at index + value
	beq  L1136	    ; branch if equal (zero)
	jsr  ClearAisTimer	    ; call subroutine
L1136:	brclr *BitFlags_50, #b50_IdleSpeedMode, R1142	 ; branch if bit(s) clear
	ldaa CoolantTemp    ; load a with memory contents
	ldx  #CLDPOS_AisColdPosition_FromTemp	 ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	brset *BitFlags_51, #b51_bit6, L1137	; branch if bit(s) set
	adda CALPOS_PositionAisMotorIsAtIdle	;  (data is 1a)
	bcs  L1138	    ; branch if lower
L1137:	brset *BitFlags_AIS, #b0c_bit4, L1139	 ; branch if bit(s) set
	adda ACOFFK_ClosedThrottleAcOffKick    ;  (data is 08)
	bcs  L1138	    ; branch if lower
	adda AC2KCK_AcClutchKickOpenAfterAcEnabled    ;  (data is 04)
	bcc  L1139	    ; branch if greater or equal
L1138:	ldaa #0xff	    ; load a with value -11111111-
L1139:	staa Temp0	    ; store a into memory
	adda AISLMH_RollingAisHighLimit    ;  (data is 20)
	bcs  L1140	    ; branch if lower
	cmpa DesiredNewAisPosition    ; compare a with memory contents
	bcs  L1141	    ; branch if lower
L1140:	ldaa Temp0	    ; load a with memory contents
	suba AISLML_RollingAisLowLimit	  ;  (data is 04)
	bcs  R1142	    ; branch if lower
	cmpa DesiredNewAisPosition    ; compare a with memory contents
	bcs  R1142	    ; branch if lower
L1141:	jsr  L1156	    ; call subroutine
	staa DesiredNewAisPosition    ; store a into memory
R1142:	rts		    ; return from subroutine

L1143:	ldaa CoolantTemp    ; load a with memory contents
	ldx  #CLDPOS_AisColdPosition_FromTemp	 ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Temp0	    ; store a into memory
	ldx  #RPMPOS_AisPosition_FromRpm    ; load index with value
	ldaa EngineRpm_HB    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	cmpa Temp0	    ; compare a with memory contents
	bcs  L1144	    ; branch if lower
	staa Temp0	    ; store a into memory
L1144:	ldaa TpsVolts	    ; load a with memory contents
	suba MINTHR_LowestSessionTPS
	bcc  L1145	    ; branch if greater or equal
	clra		    ; a = 0
L1145:	ldx  #THRPOS_AisPosition_FromThrottle	 ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	cmpa Temp0	    ; compare a with memory contents
	bcc  L1146	    ; branch if greater or equal
	ldaa Temp0	    ; load a with memory contents
L1146:	brset *BitFlags_AIS, #b0c_bit4, L1149	 ; branch if bit(s) set
	ldab ACPOS_ACPositionWhenTempToCold    ; load b with memory contents (data is 12)
	brset *BitFlags_2e, #b2e_AtIdle, L1148	  ; branch if bit(s) set
	staa Temp4	    ; store a into memory
	ldaa CoolantTemp    ; load a with memory contents
	cmpa ACTMP_Use_ACCTBL_WhenTempAboveThisElseUse_ACPOS	; compare a with memory contents (data is 7f)
	bcs  L1147	    ; branch if lower
	ldx  #ACCTBL_ACOffIdleDelta_FromSpeed	 ; load index with value
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	jsr  Lookup4ByteTable	 ; call subroutine
	brclr *BitFlags_2e, #b2e_bit2, L1147	; branch if bit(s) clear
	ldaa PERKCK_AcClutchAisAdjustmentConstant    ; load a with memory contents (data is c0)
	mul		    ; multiply (d=a*b)
	adca #0x00	    ;  -00000000-
	tab		    ; b = a
L1147:	ldaa Temp4	    ; load a with memory contents
L1148:	aba		    ; a=a+b
	bcs  L1151	    ; branch if lower
L1149:	brset *BitFlags_51, #b51_bit6, L1150	; branch if bit(s) set
	adda CALPOS_PositionAisMotorIsAtIdle	;  (data is 1a)
	bcs  L1151	    ; branch if lower
L1150:	jsr  L1156	    ; call subroutine
	cmpa AISHLM_AisHighLimitMaxOpenSteps	; compare a with memory contents (data is a0)
	bcs  L1152	    ; branch if lower
L1151:	ldaa AISHLM_AisHighLimitMaxOpenSteps	; load a with memory contents (data is a0)
L1152:	brset *BitFlags_2e, #b2e_AtIdle, L1153	  ; branch if bit(s) set
	brclr *BitFlags_AIS, #b0c_bit6, L1154	 ; branch if bit(s) clear
	brset *BitFlags_AIS, #b0c_bit7, L1154	 ; branch if bit(s) set
	cmpa DesiredNewAisPosition    ; compare a with memory contents
	bcc  L1154	    ; branch if greater or equal
	ldab Counter_MainLoop	  ; load b with memory contents
	bitb DLYOF1_UpdateRateOffIdleWhenAisClosing    ;  (data is 07)
	bne  R1155	    ; branch if not equal (not zero)
	ldaa DesiredNewAisPosition    ; load a with memory contents
	deca		    ; decrement a
L1153:	bclr *BitFlags_2e, #b2e_AtIdle	  ; clear bits
L1154:	staa DesiredNewAisPosition    ; store a into memory
R1155:	rts		    ; return from subroutine

L1156:	ldab Temp1	    ; load b with memory contents
	beq  R1159	    ; branch if equal (zero)
	staa Temp4	    ; store a into memory
	mul		    ; multiply (d=a*b)
	adca Temp4	
	bcc  R1159	    ; branch if greater or equal
	ldaa #0xff	    ; load a with value -11111111-
	rts		    ; return from subroutine

MultiplyTempvar1ByA:
	ldab Temp1	    ; load b with memory contents
	beq  R1159	    ; branch if equal (zero)
	staa Temp4	    ; store a into memory
	mul		    ; multiply (d=a*b)
	adca Temp4	
	bvc  R1159	    ; branch if overflow
	ldaa #0x7f	    ; load a with value -01111111-
	rts		    ; return from subroutine

L1157:	ldab Temp1	    ; load b with memory contents
	beq  R1159	    ; branch if equal (zero)
	nega		    ; negate a (set high bit)
	staa Temp4	    ; store a into memory
	mul		    ; multiply (d=a*b)
	adca Temp4	
	bvc  L1158	    ; branch if overflow
	ldaa #0x7f	    ; load a with value -01111111-
L1158:	nega		    ; negate a (set high bit)
R1159:	rts		    ; return from subroutine

ClearAisTimer:	
        clrb		    ; b = 0
	stab Timer_AisChanges	 ; store b into memory
StoreAndLimitDesiredAisPosition:
	tsta		    ; test a
	bmi  L1162	    ; branch if minus(hi bit 1)
	adda DesiredNewAisPosition
	ldab AISHLM_AisHighLimitMaxOpenSteps	; load b with memory contents (data is a0)
	bcs  L1161	    ; branch if lower
	cba		
	bcs  L1163	    ; branch if lower
L1161:	stab DesiredNewAisPosition    ; store b into memory
	rts		    ; return from subroutine

L1162:	adda DesiredNewAisPosition
	bcs  L1163    ; branch if lower
        clrA          ; a = 0
L1163:	staa DesiredNewAisPosition    ; store a into memory
	rts                           ; return from subroutine

; CCD Bus operation description - The bus sends 2 bytes at a time down the SPI. The first byte
; is the ID code of the data being sent, the 2nd byte is the actual data. 
;
; How to add data to bus? Maybe read the later models bus protocol...
;
; HandleCCDBusComs:
; 	sei		    ; disable interrupts
; 	ldaa PIA2_PortA_DataDirection	 ; load a with memory contents
; 	bita #pia2a_CCDBus	    ;  enable the CCD Bus chip
; 	bne  R1166	    ; branch if not equal (not zero)
; 	brset *CCDVar0, #ccd_Bit7, CCD_Error	 ; branch if bit(s) set
; 	ldd  CCDTemp_HB	; load d (a&b) with memory contents
; 	bsr  CCD_XmitCode    ; call subroutine
; 	cmpD CCDTemp_HB	; compare D
; 	beq  L1167	    ; branch if equal (zero)
; 	ldx  #PIA2_PortA_DataDirection	  ; load index with value
; 	brset  0, X, #pia2a_CCDBus, R1166    ; branch if bit(s) set
; 	ldab 0x01,x	    ; load b with memory at index + value
; 	bset  1, X, #$%00000100    ; bit set
; 	bclr  0, X, #$%00000001    ; bit clear
; 	bclr  1, X, #$%00000100    ; bit clear
; 	bset  0, X, #$%00000001    ; bit set
; 	bclr  0, X, #$%00000001    ; bit clear
; 	stab 0x01,x	
; 	bra  L1165	    ; branch
; 
; CCD_Error:
;         ldd  #0xffff	    ; load d (a&b) with value -11111111 11111111-
; 	bsr  CCD_XmitCode    ; call subroutine
; L1165:	cmpa #0xaa	    ; check the response
; 	bne  R1166	    ; branch if not equal (not zero)
; 	bset *CCDFlags2, #$%00100000    ; set error flag?
; R1166:	rts		    ; return from subroutine
; 
; L1167:	cmpa #0x84	    ; compare CCDTemp_HB to 0x84
; 	bne  L1168	    ; branch if not equal (not zero)
; 	ldab CCDFlags3    ; load b with memory contents
; 	bpl  L1168	    ; branch if plus (hi bit 0)
; 	andb #0x7f	    ;  -01111111-   was set, so now clear bit 7, in B
; 	clr  CCDFlags3    ; zero byte at memory location ; clear all flags
; 	ldaa #0xc4	    ; load a with value -11000100-
; 	stD *CCDTemp_HB	; store D to RAM
; 	bra  R1169	    ; branch
; 
; L1168:	bset *CCDVar0, #ccd_Bit7	 ; set error bit
; R1169:	rts		    ; return from subroutine
; 
; CCD_XmitCode:
; 	cmpb CPU_SerialPeripheralStatus    ; status must be checked before data is read, this command only readies the data to be read, I think
; 	staa CPU_SerialPeripheralDataIO
; 	ldx  #CPU_SerialPeripheralStatus    ; load index with value
; 	ldY #0x0005    ; load Y index -00000000 00000101-
; L1170:	brset  0, X, #bit_bit7, CCD_XmitData	 ; branch if SPIF (xfer complete) flag is set
; 	deY		    ; decrement Y
; 	bne  L1170	    ; loop until transfer is complete or times out
; 	rts		    ; return from subroutine
; 
; CCD_XmitData:
;         ldaa CPU_SerialPeripheralDataIO    ; load a with memory contents
; 	stab CPU_SerialPeripheralDataIO    ; store b into memory
; 	ldY #0x0005    ; load Y index -00000000 00000101-
; L1172:	brset  0, X, #bit_bit7, CCD_ReadResult	 ; branch if SPIF (xfer complete) flag is set
; 	deY		    ; decrement Y
; 	bne  L1172	    ; loop until transfer is complete or times out
; 	rts		    ; return from subroutine
; 
; CCD_ReadResult:
;         ldab CPU_SerialPeripheralDataIO    ; just to clear the buffer, this value is never used or stored
; 	rts		    ; return from subroutine

; PrepareCCDDataForXmit_MM:
; 	ldab Counter_MainLoop	  ; load b with memory contents
; 	andb #0x0f	    ;  -00001111-
; 	bne  L1177	    ; branch if not zero, ie. don't branch every 16 loops
; 	brset *CCDFlags1, #$%00000100, L1174    ; branch if bit(s) set
; 	ldaa KeyOnOrEngineRunningTime	 ; load a with memory contents
; 	cmpa #0x83	    ; compare a with value -10000011-
; 	bcs  L1176	    ; branch if lower
; 	ldaa EngineRpm_HB    ; load a with memory contents
; 	cmpa #0x2f	    ; compare a with value ~1500rpm
; 	bcs  L1176	    ; branch if lower
; 	ldaa BatteryVolts    ; load a with memory contents
; 	cmpa #0xbd	    ; compare a with value ~11.8v
; 	bcc  L1176	    ; branch if greater or equal
; 	ldab CCDFlags4    ; load b with memory contents
; 	incb		
; 	stab CCDFlags4    ; store b into memory
; 	cmpb #0x71	    ;  -01110001-
; 	bcs  L1177	    ; branch if lower
; 	bset *CCDFlags1, #$%00000100    ; set bits
; 	bra  L1176	    ; branch
; 
; L1174:	ldaa TargetBatteryVolts    ; load a with memory contents
; 	suba BatteryVolts
; 	bcs  L1175	    ; branch if lower
; 	cmpa #0x01	    ; compare a with value -00000001-
; 	bhi  L1176	    ; branch if higher
; L1175:	ldab CCDFlags4    ; load b with memory contents
; 	incb		
; 	stab CCDFlags4    ; store b into memory
; 	cmpb #0x22	    ;  -00100010-
; 	bcs  L1177	    ; branch if lower
; 	bclr *CCDFlags1, #$%00000100    ; clear bits
; L1176:	clr  CCDFlags4    ; zero byte at memory location
; L1177:	brset *Counter_MainLoop, #$%00000001, R1185	; branch if bit(s) set
; 	ldab CCDVar0    ; load b with memory contents
; 	incb		
; 	andb #0x7f	    ;  -01111111- clears bit 7
; 	stab Temp0	    ; store b into memory
; 	ldx  #CCDDataStream	 ; load index with value
; 	abx		    ; add b to index
; 	abx		    ; add b to index
; 	ldx  0x00,x	
; 	ldaa CCDTemp_HB	; load a with memory contents
; 	sei		    ; disable interrupts
; 	brset *CCDVar0, #ccd_Bit7, L1183	 ; branch if bit(s) set
; 	bset *CCDVar0, #ccd_Bit7	 ; set bits
; 	cmpa #0x84	    ; compare a with value -10000100-
; 	bne  L1181	    ; branch if not equal (not zero)
; 	cpx  #CCD_SpeedSensorCounter    ;  -10010011 11100111-
; 	bne  L1179	    ; branch if not equal (not zero)
; 	ldab CCDFlags3    ; load b with memory contents
; 	andb #0x7f	    ;  -01111111-
; 	addb Counter_SpeedSensorInterrupt_HB    ; b=b+memory contents
; 	bpl  L1178	    ; branch if plus (hi bit 0)
; 	ldab #0x7f	    ; load b with value -01111111-
; L1178:	orab #0x80	    ;  -10000000-
; 	stab CCDFlags3    ; store b into memory
; 	clr  Counter_SpeedSensorInterrupt_HB    ; zero byte at memory location
; 	bra  L1184	    ; branch
; 
; L1179:	cpx  #CCD_FuelOutput    ;  -10010011 11011111-
; 	bne  L1184	    ; branch if not equal (not zero)
; 	ldab CCDTemp_LB	; load b with memory contents
; 	addb CCDFuelOutput_HB    ; b=b+memory contents
; 	bcc  L1180	    ; branch if greater or equal
; 	ldab #0xff	    ; load b with value -11111111-
; L1180:	stab CCDTemp_LB	; store b into memory
; 	clr  CCDFuelOutput_HB    ; zero byte at memory location
; 	bra  L1184	    ; branch
; 
; L1181:	cmpa #0xc4	    ; compare a with value -11000100-
; 	bne  L1183	    ; branch if not equal (not zero)
; 	cpx  #CCD_SpeedSensorCounter    ;  -10010011 11100111-
; 	bne  L1184	    ; branch if not equal (not zero)
; 	ldab CCDTemp_LB	; load b with memory contents
; 	addb Counter_SpeedSensorInterrupt_HB    ; b=b+memory contents
; 	bcc  L1182	    ; branch if greater or equal
; 	ldab #0xff	    ; load b with value -11111111-
; L1182:	stab CCDTemp_LB	; store b into memory
; 	clr  Counter_SpeedSensorInterrupt_HB    ; zero byte at memory location
; 	bra  L1184	    ; branch
; 
; L1183:	cli		    ; enable interrupts
; 	jsr  0x00,x	
; 	stD *CCDTemp_HB	    ; store D to RAM
; L1184:	ldaa Temp0	    ; load a with memory contents
; 	staa CCDVar0        ; store a into memory
; 	cli		    ; enable interrupts
; R1185:	rts		    ; return from subroutine
; 
; CCD_OutputStatus:
; 	ldaa Temp0	    ; load a with memory contents
; 	oraa #0x80	    ;  -10000000- set bit 7
; 	staa CCDVar0    ; store a into memory
; 	pulx		    ; pull index from stack
; 	rts		    ; return from subroutine
; 
; CCD_EngineRPM:
; 	ldaa #0xe4	    ; load a with value -11100100-
; 	ldab EngineRpm_HB    ; load b with memory contents
; 	rts		    ; return from subroutine
; 
; CCD_MAP: ldaa #0x94	    ; load a with value -10010100-
; 	ldab MapValue	    ; load b with memory contents
; 	rts		    ; return from subroutine
; 
; CCD_FuelOutput:
; 	ldaa #0x84	    ; load a with value -10000100-
; 	ldab CCDFuelOutput_HB    ; load b with memory contents
; 	clr  CCDFuelOutput_HB    ; zero byte at memory location
; 	rts		    ; return from subroutine
; 
; CCD_SpeedSensorCounter:
; 	ldaa #0xc4	    ; load a with value -11000100-
; 	ldab CCDFlags3    ; load b with memory contents
; 	bpl  L1186	    ; branch if plus (hi bit 0)
; 	andb #0x7f	    ;  -01111111-
; 	bra  L1187	    ; branch
; 
; L1186:	ldab Counter_SpeedSensorInterrupt_HB    ; load b with memory contents
; 	clr  Counter_SpeedSensorInterrupt_HB    ; zero byte at memory location
; L1187:	clr  CCDFlags3    ; zero byte at memory location
; 	rts		    ; return from subroutine
; 
; CCD_CONST800F:
; 	ldaa #0xac	    ; load a with value -10101100-
; 	ldab CCDCFG_CCDConfigConstant	  ; load b with memory contents (data is 22)
; 	rts		    ; return from subroutine
; 
; CCD_BatVoltsEtc:
; 	ldaa BatteryVolts    ; load a with memory contents
; 	ldab BitFlags_52    ; load b with memory contents
; 	bitb #b52_DRBToggle1 | b52_DRBToggle2	       ;  -00000011-
; 	bne  L1189	    ; branch if not equal (not zero)
; 	ldab CCDBTV_CCDBatteryVoltsOutput    ; load b with memory contents (data is ff)
; 	cmpb #0x10	    ;  -00010000-
; 	bhi  L1189	    ; branch if higher
; 	comb		
; 	cmpb LB7E1	    ; compare b with memory contents (data is ff)
; 	bne  L1189	    ; branch if not equal (not zero)
; 	addb #0x09	    ;  -00001001-
; 	bcs  L1188	    ; branch if lower
; 	mul		    ; multiply (d=a*b)
; 	adca #0x00	    ;  -00000000-
; 	bra  L1189	    ; branch
; 
; L1188:	staa Temp1	    ; store a into memory
; 	mul		    ; multiply (d=a*b)
; 	adca Temp1	
; 	bcc  L1189	    ; branch if greater or equal
; 	ldaa #0xff	    ; load a with value -11111111-
; L1189:	tab		    ; b = a
; 	ldaa #0xd4	    ; load a with value -11010100-
; 	rts		    ; return from subroutine
; 
; CCD_CoolantTemp:
; 	ldaa #0x8c	    ; load a with value -10001100-
; 	ldab CoolantTemp    ; load b with memory contents
; 	rts		    ; return from subroutine
; 
; CCD_TargetIdleSpeed_HB:
; 	ldd  TargetIdleSpeed_HB	; load d (a&b) with memory contents
; 	asld		    ; shift left (d=d*2)
; 	asld		    ; shift left (d=d*2)
; 	tab		    ; b = a
; 	ldaa #0xcc	    ; load a with value -11001100-
; 	rts		    ; return from subroutine
; 
; CCD_ThrottlePos:
; 	ldab TpsVolts	    ; load b with memory contents
; 	subb MINTHR_LowestSessionTPS	; b = b-memory contents
; 	bcc  L1190	    ; branch if greater or equal
; 	clrb		    ; b = 0
; L1190:	ldaa #0x42	    ; load a with value -01000010-
; 	rts		    ; return from subroutine
; 
; CCD_SwitchState:
; 	clrb		    ; b = 0
; 	brset *PIA1_A_Buffer, #pia1abuf_CELight, L1191	  ; branch if bit(s) set
; 	orab #0x01	    ;  -00000001-
; L1191:	brset *PIA1_A_Buffer, #pia1abuf_PartThrotUnlock, L1192	  ; branch if bit(s) set
; 	orab #0x40	    ;  -01000000-
; L1192:	brclr *b45_IPL1, #b45_BattNotCharging, L1193    ; branch if bit(s) clear
; 	orab #0x08	    ;  -00001000-
; L1193:	ldaa TpsVolts	    ; load a with memory contents
; 	suba MINTHR_LowestSessionTPS
; 	bcs  L1194	    ; branch if lower
; 	cmpa #0x05	    ; compare a with value -00000101-
; 	bcs  L1194	    ; branch if lower
; 	orab #0x02	    ;  -00000010-
; L1194:	brclr *CCDFlags1, #$%00000100, L1195    ; branch if bit(s) clear
; 	orab #0x04	    ;  -00000100-
; L1195:	brclr *StartupSwitchMirror2, #sw2_Brake, L1196	 ; branch if bit(s) clear
; 	orab #0x10	    ;  -00010000-
; L1196:	brclr *StartupSwitchMirror2, #sw2_ACclutch, L1197    ; branch if bit(s) clear
; 	orab #0x20	    ;  -00100000-
; L1197:	stab CCDFlags1    ; store b into memory
; 	ldaa #0xa4	    ; load a with value -10100100-
; 	rts		    ; return from subroutine
; 
; CCD_ToggleCCDFlags:
; 	clrb		    ; b = 0
; 	brclr *b45_IPL1, #b45_TpsBadSignal, L1198	; branch if bit(s) clear
; 	orab #0x02	    ;  -00000010-
; L1198:	sei		    ; disable interrupts
; 	ldaa CCDFlags2    ; load a with memory contents
; 	anda #0x20	    ; AND a with value -00100000-
; 	aba		    ; a=a+b
; 	tab		    ; b = a
; 	anda #0xdf	    ; AND a with value -11011111-
; 	staa CCDFlags2    ; store a into memory
; 	cli		    ; enable interrupts
; 	ldaa #0xec	    ; load a with value -11101100-
; 	rts		    ; return from subroutine
; 
; CCD_AmbientAirTemp:
; 	ldaa #0x4c	    ; load a with value -01001100-
; 	ldab AmbientAirTempVolts    ; load b with memory contents
; 	rts		    ; return from subroutine
; 
; CCD_B600:
; 	ldd  LB600	    ;  (data is ffff)
; 	asld		    ; shift left (d=d*2)
; 	asld		    ; shift left (d=d*2)
; 	tab		    ; b = a
; 	ldaa #0x2c	    ; load a with value -00101100-
; 	rts		    ; return from subroutine
; 
; 
; 	    ;.org	0x949c
; 	    CCDDataStream:
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_FuelOutput
; 		.word	CCD_SpeedSensorCounter
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_AmbientAirTemp
; 		.word	CCD_ToggleCCDFlags
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_B600
; 		.word	CCD_TargetIdleSpeed_HB
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_SwitchState
; 		.word	CCD_ThrottlePos
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_FuelOutput
; 		.word	CCD_SpeedSensorCounter
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_OutputStatus
; 		.word	CCD_OutputStatus
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_BatVoltsEtc
; 		.word	CCD_OutputStatus
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_SwitchState
; 		.word	CCD_ThrottlePos
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_FuelOutput
; 		.word	CCD_SpeedSensorCounter
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_OutputStatus
; 		.word	CCD_OutputStatus
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_OutputStatus
; 		.word	CCD_OutputStatus
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_SwitchState
; 		.word	CCD_ThrottlePos
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_FuelOutput
; 		.word	CCD_SpeedSensorCounter
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_OutputStatus
; 		.word	CCD_OutputStatus
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_CoolantTemp
; 		.word	CCD_OutputStatus
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_SwitchState
; 		.word	CCD_ThrottlePos
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_FuelOutput
; 		.word	CCD_SpeedSensorCounter
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_CONST800F
; 		.word	CCD_OutputStatus
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_OutputStatus
; 		.word	CCD_OutputStatus
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_SwitchState
; 		.word	CCD_ThrottlePos
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_FuelOutput
; 		.word	CCD_SpeedSensorCounter
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_OutputStatus
; 		.word	CCD_OutputStatus
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_BatVoltsEtc
; 		.word	CCD_OutputStatus
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_SwitchState
; 		.word	CCD_ThrottlePos
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_FuelOutput
; 		.word	CCD_SpeedSensorCounter
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_OutputStatus
; 		.word	CCD_OutputStatus
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_OutputStatus
; 		.word	CCD_OutputStatus
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_SwitchState
; 		.word	CCD_ThrottlePos
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_FuelOutput
; 		.word	CCD_SpeedSensorCounter
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_OutputStatus
; 		.word	CCD_OutputStatus
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_CoolantTemp
; 		.word	CCD_OutputStatus
; 		.word	CCD_EngineRPM
; 		.word	CCD_MAP
; 		.word	CCD_SwitchState
; 		.word	CCD_ThrottlePos

HandleO2Processing_MM:
	clra		    ; a = 0
	ldab MapValue	    ; load b with memory contents
	cmpb MAPDEC_NoCellUpdateAndO2CNTRHeldBelowThisMap    ; compare b with memory contents (data is 0d)
	bls  O2_SetStayOpenLoopFlag	    ; branch if lower or same
	ldab Timer_O2InhibitSwitchingRichIdleToClosedLoop    ; load b with memory contents
	bne  O2_SetStayOpenLoopFlag	    ; branch if not equal (not zero)
	ldab Timer_OpenLoopFraction    ; load b with memory contents
	beq  O2_ClearStayOpenLoopFlag	    ; branch if equal (zero)
	brset *BitFlags_4f, #b4f_OffIdle, O2_SetStayOpenLoopFlag    ; branch if bit(s) set

O2_ClearStayOpenLoopFlag:
	bclr *BitFlags_50, #b50_StayOpenLoop	; clear bits
	bra  L1201	    ; branch

O2_SetStayOpenLoopFlag:	
        bset *BitFlags_50, #b50_StayOpenLoop	; set bits
	staa Counter_PrimaryRamp	  ; clear ramp counter
L1201:	brset *BitFlags_4f, #b4f_FullThrottle, O2_FullThrottle	  ; branch if bit(s) set
	brclr *BitFlags_4f, #b4f_PTEisMaxed, L1202    ; branch if bit(s) clear
	brclr *BitFlags_50, #b50_StayOpenLoop, L1202	; branch if bit(s) clear
O2_FullThrottle:
	brset *BitFlags_4f, #b4f_O2Valid, O2_StopUsingFeedback	  ; branch if bit(s) set
	bra  L1203	    ; branch

L1202:	brset *BitFlags_4f, #b4f_O2Valid, O2_UsingFeedback    ; branch if bit(s) set
L1203:	ldab CoolantTemp    ; load b with memory contents
	cmpb CLTEMP_TempToStartCLTIMETimer    ; compare b with memory contents (data is 92)
	bcs  O2_StopUsingFeedback    ; branch if lower
	brset *BitFlags_4f, #b4f_OpenLoop, L1205    ; branch if bit(s) set
	ldab Counter_MainLoop	  ; load b with memory contents
	bne  O2_StopUsingFeedback    ; branch if not equal (not zero)
	ldab Timer_CLTIME_ClosedLoopTimer    ; load b with memory contents
	beq  L1204	    ; branch if equal (zero)
	decb		
	stab Timer_CLTIME_ClosedLoopTimer    ; store b into memory
	bne  O2_StopUsingFeedback    ; branch if not equal (not zero)
L1204:	bset *BitFlags_4f, #b4f_OpenLoop    ; set bits
L1205:	ldab O2SensorValue    ; load b with memory contents
	cmpb O2HIGH_HighLimitForImmediateSwitchToClosedLoop    ; compare b with memory contents (data is 26)
	bcc  O2_ValidSignal_OutsideMiddleRange	  ; branch if greater or equal
	cmpb O2LOW_LowLimitForImmediateSwitchToClosedLoop    ; compare b with memory contents (data is 0f)
	bcc  O2_InvalidSignal_InMiddleRange    ; branch if greater or equal
O2_ValidSignal_OutsideMiddleRange:
	bset *BitFlags_4f, #b4f_O2Valid    ; set bits
	staa Counter_AdaptiveMem_Erase	  ; store a into memory
	clrb		    ; b = 0
	bra  L1208	    ; branch

O2_InvalidSignal_InMiddleRange:
	brset *Timer_CLTIME_ClosedLoopTimer, #bit_bit7, L1207	 ; branch if bit(s) set
	cmpb O2TLMH_HighLimitForDelayedSwitchToClosedLoop    ; compare b with memory contents (data is 1f)
	bcc  L1206	    ; branch if greater or equal
	cmpb O2TLML_LowLimitForDelayedSwitchToClosedLoop    ; compare b with memory contents (data is 0f)
	bcc  O2_StopUsingFeedback    ; branch if greater or equal
L1206:	bset *Timer_CLTIME_ClosedLoopTimer, #bit_bit7	 ; set bits
L1207:	ldab Counter_MainLoop	  ; load b with memory contents
	bne  O2_StopUsingFeedback    ; branch if not equal (not zero)
	ldab Timer_CLTIME_ClosedLoopTimer    ; load b with memory contents
	cmpb O2TIME_DelayTimeToClosedLoop    ; compare b with memory contents (data is 07)
	bmi  O2_ValidSignal_OutsideMiddleRange	  ; branch if minus(hi bit 1)
	incb		
L1208:	stab Timer_CLTIME_ClosedLoopTimer    ; store b into memory
O2_StopUsingFeedback:
	staa Counter_PrimaryAndSecondaryRamp    ; store a into memory
	staa Counter_PrimaryRamp	  ; store a into memory
	bset *BitFlags_50, #b50_StayOpenLoop | b50_OpenLoop    ; set bits
	rts		    ; return from subroutine

O2_UsingFeedback:
	ldab O2SensorValue    ; load b with memory contents
	cmpb O2MIDH_HighLimitForInMiddleDetermination	 ; compare b with memory contents (data is 1c)
	bcc  O2Signal_InOuterMiddleRange    ; branch if greater or equal
	cmpb O2MIDL_LowLimitForInMiddleDetermination	; compare b with memory contents (data is 12)
	bcs  O2Signal_InOuterMiddleRange    ; branch if lower
	ldaa Timer_CLTIME_ClosedLoopTimer    ; load a with memory contents
	inca		    ; increment a
	bne  L1209	    ; branch if not equal (not zero)
	jmp  Save_CLTIME_ToOtherTimers_O2InMiddle

L1209:	brset *Counter_MainLoop, #$%00000001, L1210	; branch if bit(s) set
O2Signal_InOuterMiddleRange:
	staa Timer_CLTIME_ClosedLoopTimer    ; store a into memory
L1210:	clra		    ; a = 0
	cmpb O2HSWP_HighLimitForO2RampSwitching    ; compare b with memory contents (data is 19)
	bcc  O2Signal_AboveToggle    ; branch if greater or equal
	cmpb O2LSWP_LowLimitForO2RampSwitching	  ; compare b with memory contents (data is 18)
	bcs  O2Signal_BelowToggle    ; branch if lower
	rts		    ; return from subroutine

O2Signal_AboveToggle:
	deca		    ; decrement a
O2Signal_BelowToggle:
	ldab CALTHR_O2ControllerDeadbandLimitForUpdatingCells	 ; load b with memory contents (data is 09)
	staa Temp0	    ; store a into memory
	bmi  L1211	    ; branch if minus(hi bit 1)
	negb		
L1211:	addb Counter_PrimaryAndSecondaryRamp    ; b=b+memory contents
	bvs  SwitchOrStayOpenLoop    ; branch if no overflow
	eorb Temp0	
	bmi  SwitchOrStayOpenLoop    ; branch if minus(hi bit 1)
	ldab CONFIG_ConfigurationFlags	  ; load b with memory contents (data is 02)
	bitb #cfg_ATX		;  -00100000-
	beq  L1212	    ; branch if equal (zero)
	brclr *BitFlags_AIS, #b0c_ATXInGear, SwitchOrStayOpenLoop    ; branch if bit(s) clear
L1212:
	ldab MapValue	    ; load b with memory contents
	cmpb MAPLIM_NoCellUpdateAboveThisMAP	; compare b with memory contents (data is 66)
	bhi  SwitchOrStayOpenLoop    ; branch if higher
	cmpb MAPDEC_NoCellUpdateAndO2CNTRHeldBelowThisMap    ; compare b with memory contents (data is 0d)
	bls  SwitchOrStayOpenLoop    ; branch if lower or same
	ldab EngineRpm_HB    ; load b with memory contents
	cmpb RPMLIM_NoCellUpdateAboveThisRPMInRPMOver32    ; compare b with memory contents (data is 56)
	bhi  SwitchOrStayOpenLoop    ; branch if higher
	ldab Factor_DecelLeanoutWhenMAPDecreasing    ; load b with memory contents
	orab Timer_OffThrottleFuelEnrich
	orab Timer_OpenLoopFraction
	orab Timer_O2CNTR_CountdownFromAbove196FtoEnableClosedLoop
	bne  SwitchOrStayOpenLoop    ; branch if not equal (not zero)
	ldaa MapValue	    ; load a with memory contents
	cmpa BOOSTP_AdjustO2ResponseForPTEWhenMapAboveThis    ; compare a with memory contents (data is ff)
	bcc  SwitchOrStayOpenLoop    ; branch if greater or equal
	bclr *BitFlags_50, #b50_OpenLoop    ; clear bits
	bra  SwitchOrStayClosedLoop    ; branch

SwitchOrStayOpenLoop:
	bset *BitFlags_50, #b50_OpenLoop    ; set bits
SwitchOrStayClosedLoop:
	clra		    ; a = 0
	ldab Temp0	    ; load b with memory contents
	eorb BitFlags_4f
	andb #b4f_O2Rich	  ;  -00000100-
	beq  O2HasNotToggled	; branch if equal (zero)
	eorb BitFlags_4f
	stab BitFlags_4f    ; store b into memory
	clrb		    ; b = 0
	ldaa Counter_PrimaryRamp	  ; load a with memory contents
	stab Counter_PrimaryRamp	  ; store b into memory
	stab Timer_O2ToggleDuration    ; store b into memory
	bclr *BitFlags_2e, #b2e_BadO2Read	; clear bits
	brclr *BitFlags_50, #b50_StayOpenLoop, WorkWithPrimaryRamp    ; branch if bit(s) clear
	stab Counter_AdaptiveMem_Erase	  ; store b into memory
	rts		    ; return from subroutine

O2HasNotToggled:
	ldab Counter_PrimaryRamp	  ; load b with memory contents
	beq  CheckAndSetO2FaultCode	    ; branch if equal (zero)
WorkWithPrimaryRamp:
	staa Temp0	    ; clear Temp0 since A was previoulsly cleared
	ldx  #PRIRMP_PrimaryRamp    ; load index with value
	jsr  DetermineRampCellFromRPMandMAP    ; call subroutine
	ldab Counter_PrimaryRamp	  ; load b with memory contents
	addb 0x00,x	    ; add ramp value to timer value
	sba		    ; subtract (ramp+timer) from limit
	bhi  PrimaryRampWithinLimit	    ; branch if limit is higher than ramp+timer
	adda 0x00,x	    ; add ramp value back to (limit-(ramp+timer)) = limit-timer
	bpl  L1213	    ; branch if plus (hi bit 0)
	clra		    ; a = 0
L1213:	clrb		    ; b = 0
	stab Counter_PrimaryRamp	  ; store b into memory
	bra  L1215	    ; branch

PrimaryRampWithinLimit:	
        ldaa 0x00,x	    ; load a with memory at index + value
	tab		    ; b = a
	addb Counter_PrimaryRamp	  ; b=b+memory contents
	stab Counter_PrimaryRamp	  ; store b into memory
L1215:	ldab Temp0	    ; load b with memory contents
	beq  L1216	    ; branch if equal (zero)
	cba		
	bcs  L1216	    ; branch if lower
	tba		    ; a = b
L1216:	ldab BitFlags_4f    ; load b with memory contents
	bitb #b4f_O2Rich	  ;  -00000100-
	beq  L1217	    ; branch if equal (zero)
	nega		    ; negate a (set high bit)
L1217:	jsr  PriAndSecRamp_IncrementO2SensorFeedbackCount    ; call subroutine
	clra		    ; a = 0
	bra  L1219	    ; branch

CheckAndSetO2FaultCode:	
        brset *BitFlags_50, #b50_StayOpenLoop, R1220	; branch if bit(s) set
	ldaa Counter_AdaptiveMem_Erase	  ; load a with memory contents
	cmpa LTHTIM_IfNoO2SwitchForThisTimeThrowFault51or52    ; compare a with memory contents (data is 2b)
	bcc  EraseAdaptiveMemory_possiblySetErrorBit	; branch if greater or equal
	ldab Counter_MainLoop	  ; load b with memory contents
	bne  R1220	    ; branch if not equal (not zero)
	inca		    ; increment a
L1219:	staa Counter_AdaptiveMem_Erase	  ; store a into memory
R1220:	rts		    ; return from subroutine

EraseAdaptiveMemory_possiblySetErrorBit:
	brset *BitFlags_2e, #b2e_BadO2Read, L1221	; branch if bit(s) set
	inc  BitFlags_2e
	bra  EraseAdaptiveMemory1    ; branch

L1221:	ldd  #0x0381	    ; load d (a&b) with value -00000011 10000001-
	brset *BitFlags_4f, #b4f_O2Rich, L1222	  ; branch if bit(s) set
	inca		    ; increment a
L1222:	jsr  ThrowNonCriticalError    ; call subroutine
	bcc  R1224	    ; branch if greater or equal
	bset *BitFlags_50, #b50_BadO2	 ; set bits
	bclr *BitFlags_2e, #b2e_BadO2Read	; clear bits
EraseAdaptiveMemory1:
	clra		    ; a = 0
	staa ValueFromAdaptiveMemory	; store a into memory
	ldx  #AutoCalCell0    ; load index with value
L1223:	staa 0x00,x
	inx		    ; increment index (x=x+1)
	cpx  #AutoCalCell0+0x0f    ;  -00000000 00011110-
	bne  L1223	    ; branch if not equal (not zero)
Save_CLTIME_ToOtherTimers_O2InMiddle:
	staa AdaptiveCellUpdateTimer_IncrementedEveryDistRisingEdge    ; store a into memory
	staa Counter_AdaptiveMem_Erase	  ; store a into memory
	staa Timer_CLTIME_ClosedLoopTimer    ; store a into memory
	bclr *BitFlags_4f, #b4f_O2Valid    ; clear bits
R1224:	rts		    ; return from subroutine

ModifyO2FeedbackCountVarToMaintainStoich_MM:
	brset *BitFlags_50, #b50_StayOpenLoop, L1225	; branch if bit(s) set
	brset *BitFlags_4f, #b4f_O2Valid, WorkWithSecondaryRamp    ; branch if bit(s) set
L1225:	clra		    ; a = 0
	staa Timer_O2ToggleDuration    ; store a into memory
	rts		    ; return from subroutine

WorkWithSecondaryRamp:
	ldx  #SECRMP_SecondaryRamp    ; load index with value
	bsr  DetermineRampCellFromRPMandMAP    ; call subroutine
	sei		    ; disable interrupts
	ldaa Timer_O2ToggleDuration    ; load a with memory contents
	brclr *EGRVar2, #bit_bit7, L1226	; branch if bit(s) clear
	suba SCRMP1_SecondaryRampSubtractor1	;  (data is 02)
	bra  L1227	    ; branch

L1226:	sba		    ; (Timer_O2Toggle - limit value)
L1227:	bcc  O2_SensorStuckOnOneSideTooLong    ; branch if the timer is greater than the limit value, timer expired
	cli		    ; enable interrupts
	rts		    ; return from subroutine

O2_SensorStuckOnOneSideTooLong:
	staa Timer_O2ToggleDuration    ; store a into memory
	cli		    ; enable interrupts
	ldaa 0x00,x	    ; load a with ramp value
PriAndSecRamp_IncrementO2SensorFeedbackCount:
	ldab O2LIMH_O2RangeLimitHigh    ; load b with memory contents (data is 7f)
	adda Counter_PrimaryAndSecondaryRamp
	bvc  DIDNT_2SCOMPLEMENT_OVERFLOW_UNDERFLOW1    ; branch if overflow
	brclr *Counter_PrimaryAndSecondaryRamp, #bit_bit7, SetCounterToMaxMinValue    ; branch if bit(s) clear
	ldab O2LIML_O2RangeLimitLow    ; load b with memory contents (data is b3)
	bra  SetCounterToMaxMinValue	; branch

DIDNT_2SCOMPLEMENT_OVERFLOW_UNDERFLOW1:
	cba		              ; b=O2LIMH, A=Counter_O2SensorFeedback+RampValue
	bge  SetCounterToMaxMinValue  ; branch if Counter+Ramp is > O2LIMH
	ldab O2LIML_O2RangeLimitLow   ; load b with memory contents (data is b3)
	cba		              ; b=O2LIML, A=Counter_O2SensorFeedback+RampValue
	bge  IncrementCounterByRampValue	              ; branch if Counter+Ramp is > O2LIML
SetCounterToMaxMinValue:
	tba		    ; a = b
IncrementCounterByRampValue:
	brclr *BitFlags_50, #b50_BadO2, UpdateO2FeedbackCount	 ; branch if bit(s) clear
	tsta		    ; test a
	bmi  DontUpdateO2FeedbackCount	  ; branch if minus(hi bit 1)
UpdateO2FeedbackCount:
        staa Counter_PrimaryAndSecondaryRamp    ; store a into memory
DontUpdateO2FeedbackCount:
	rts		    ; return from subroutine

DetermineRampCellFromRPMandMAP:
	brset *BitFlags_50, #b50_FallToIdle, FindCruiseCell    ; branch if bit(s) set
	brset *BitFlags_4f, #b4f_OffIdle, FindCruiseCell    ; branch if bit(s) set
	ldab #0x16	    ; Point to the idle cell...
	bra  DecideRichOrLeanValue	    ; branch

FindCruiseCell:
	clrb		    ; b = 0
	ldaa EngineRpm_HB    ; load a with memory contents
FindRPMCell:
        cmpa 0x00,x	    ; compare a with memory at index + value
	bcs  CheckRPMCell   ; branch if RPM cell boundary is greater than actual RPM
	incb		    ; b=b+1
	inx		    ; increment index (x=x+1)
	cmpb #0x02	    ; 3 looops only
	bcs  FindRPMCell    ; branch if lower
	bra  L1234	    ; branch if end of RPM range

CheckRPMCell:
	tstb
	bne  L1233	    ; branch if not equal (not zero)
	inx		    ;
L1233:	inx		    ; point to the MAP cells
L1234:	ldaa MapValue	    ; load a with memory contents
FindMAPCell:
        cmpa 0x00,x	    ; compare a with memory at index + value
	bcs  L1236	    ; branch if MAP cell boundary is lower than actual MAP
	addb #0x03	    ;  -00000011-
	inx		    ; increment index (x=x+1)
	cmpb #0x06	    ;  -00000110-
	bcs  FindMAPCell    ; branch if lower
	bra  L1238	    ; branch if end of MAP range

L1236:	cmpb #0x03	    ;  -00000011-
	bcc  L1237	    ; branch if greater or equal
	inx		    ; increment index (x=x+1)
L1237:	inx		    ; increment index (x=x+1)
L1238:	lslb
DecideRichOrLeanValue:
        brclr *BitFlags_4f, #b4f_O2Rich, LoadCellValue	  ; branch if bit(s) clear
	incb		
LoadCellValue:	
        abx		    ; add b to index
	ldaa 0x14,x	    ; load a with memory at index + value
	tab		    ; b = a
	rts		    ; return from subroutine

;
; Return values:
; - A and B contain the limit value for the selected cell, rich/lean
; - X contains the address to the kick value for the selected cell, rich/lean
;

AdaptiveMemory_UpdateCellIfRequired_MM:
	ldx  #AutoCalCell0    ; load index with value
	ldab PointerIntoAdaptiveMemory	  ; load b with memory contents
	abx		    ; add b to index
	ldab AMUPDT_EPPsBetweenCalChangeUpdateOpenThrottle    ; load b with memory contents (data is 1a)
	brset *BitFlags_4f, #b4f_OffIdle, UpdateAdaptive_OffIdle    ; branch if bit(s) set
	ldab AMUPDI_EPPsBetweenCalChangeUpdateClosedThrottle	; load b with memory contents (data is 1a)
UpdateAdaptive_OffIdle:
	brset *BitFlags_50, #b50_OpenLoop, DontUpdateCell_MaybeUpdateTimer    ; branch if bit(s) set
	stab Temp0	    ; store b into memory
	ldd  InjectorPulsewidth_HB    ; load d (a&b) with memory contents
	addd Pulsewidth_PartThrottleEnrichment_HB    ; d = d + memory contents
	subd PWMIN_NoCellUpdateBelow_PWMIN_Pulsewidth	 ;  (data is 0113)
	ldab Temp0	    ; load b with memory contents
	bcs  DontUpdateCell_MaybeUpdateTimer	; branch if lower
	sei		    ; disable interrupts
	ldaa AdaptiveCellUpdateTimer_IncrementedEveryDistRisingEdge    ; load a with memory contents
	sba		    ; subtract (a=a-b)
	bcs  DontUpdateCellOrTimer    ; branch if lower
	staa AdaptiveCellUpdateTimer_IncrementedEveryDistRisingEdge    ; store a into memory
	cli		    ; enable interrupts
	ldaa CELCHG_BitsChangePerUpdateWithinACell    ; load a with memory contents (data is 01)
	ldab Counter_PrimaryAndSecondaryRamp    ; load b with memory contents
	bpl  L1241	    ; branch if plus (hi bit 0)
	nega		    ; negate a (set high bit)
L1241:	ldab AMLIMH_MaxMultiplierCannotBeAbove7F    ; load b with memory contents (data is 7f)
	adda 0x00,x	
	bvc  Adaptive_Overflowed    ; branch if overflow
	ldaa 0x00,x	    ; load a with memory at index + value
	bpl  Adaptive_SetCellToMaxOrMinValue	; branch if plus (hi bit 0)
	ldab AMLIML_MinMultiplierCannotBeBelow80    ; load b with memory contents (data is b3)
	bra  Adaptive_SetCellToMaxOrMinValue	; branch

Adaptive_Overflowed:
	cba		
	bge  Adaptive_SetCellToMaxOrMinValue	; branch if greater or equal
	ldab AMLIML_MinMultiplierCannotBeBelow80    ; load b with memory contents (data is b3)
	cba		
	bge  L1242	    ; branch if greater or equal
Adaptive_SetCellToMaxOrMinValue:
	tba		    ; a = b
L1242:	staa 0x00,x
DontUpdateCellOrTimer:
	cli		    ; enable interrupts
	ldaa 0x00,x	    ; load a with memory at index + value
	staa ValueFromAdaptiveMemory	; store a into memory
	rts		    ; return from subroutine

DontUpdateCell_MaybeUpdateTimer:
	ldaa 0x00,x	    ; load a with memory at index + value
	staa ValueFromAdaptiveMemory	; store a into memory
	ldaa AdaptiveCellUpdateTimer_IncrementedEveryDistRisingEdge    ; load a with memory contents
	cba		
	bcs  R1243	    ; branch if lower
	stab AdaptiveCellUpdateTimer_IncrementedEveryDistRisingEdge    ; store b into memory
R1243:	rts		    ; return from subroutine

AdaptiveMemory_DetermineWhichCellApplies_MM:
	clra		    ; a = 0
	staa Temp0	    ; store a into memory
	ldx  #MP1_AutoCalMapCellBoundary1    ; load index with value
	ldaa BitFlags_4f    ; load a with memory contents
	bmi  ONTHROTTLE_OR_RPMTOOHIGHFORIDLE	; branch if minus(hi bit 1)
	ldab #0x0c	    ; load b with value -00001100-
	ldaa TargetIdleSpeed_HB	; load a with memory contents
	adda IDLOFS_DeltaForIdleRPMForClosedThrottleCell    ;  (data is 04)
	cmpb PointerIntoAdaptiveMemory
	bne  L1244	    ; branch if not equal (not zero)
	adda HYTRPM_HysteresisFor_IDLOFS    ;  (data is 02)
L1244:	cmpa EngineRpm_HB    ; compare a with memory contents
	bcs  ONTHROTTLE_OR_RPMTOOHIGHFORIDLE	; branch if lower
	bra  L1250	    ; branch

L1245:	ldaa 0x00,x	    ; load a with memory at index + value
	cmpb Temp0	
	bcc  L1246	    ; branch if greater or equal
	adda DLTMAP_MapHysteresisAtMapCellBoundaries	;  (data is 01)
L1246:	cmpa MapValue	    ; compare a with memory contents
	bcc  L1247	    ; branch if greater or equal
	inx		    ; increment index (x=x+1)
ONTHROTTLE_OR_RPMTOOHIGHFORIDLE:
	ldab PointerIntoAdaptiveMemory	  ; load b with memory contents
	inc  Temp0	
	inc  Temp0	
	cpx  #DLTMAP_MapHysteresisAtMapCellBoundaries	 ;  -10000100 01001010-
	bne  L1245	    ; branch if not equal (not zero)
L1247:	ldaa R1_RPMCellBoundaryInRPMover32    ; load a with memory contents (data is 32)
	lsrb		    ; logical shift right b
	bcs  L1248	    ; branch if lower
	adda DLTRPM_DeltaRPMAtRPMBoundariesInRPMOver32	  ;  (data is 02)
L1248:	ldab Temp0	    ; load b with memory contents
	cmpa EngineRpm_HB    ; compare a with memory contents
	bcs  L1249	    ; branch if lower
	decb		
L1249:	decb
L1250:	cmpb PointerIntoAdaptiveMemory
	beq  L1251	    ; branch if equal (zero)
	clr  AdaptiveCellUpdateTimer_IncrementedEveryDistRisingEdge    ; zero byte at memory location
L1251:	stab PointerIntoAdaptiveMemory	  ; store b into memory
	rts		    ; return from subroutine

HandleAmTimer_MM:
	brclr *BitFlags_54, #b54_FuelEngineNotRunning, AmTimer_EngineRunning	 ; branch if bit(s) clear
	ldaa CoolantTemp    ; load a with memory contents
	ldx  #AMTPSW_TempPointToEnableSelectedAMTimer	 ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Timer_O2CNTR_CountdownFromAbove196FtoEnableClosedLoop    ; store a into memory
	ldaa CoolantTemp    ; load a with memory contents
	ldx  #CLTIME_ClosedLoopTimeFromEngTempAtStartup_FromTemp    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Timer_CLTIME_ClosedLoopTimer    ; store a into memory
	bclr *BitFlags_4f, #b4f_OpenLoop    ; clear bits
AmTimer_EngineRunning:
	ldaa CoolantTemp    ; load a with memory contents
	ldab Counter_MainLoop	  ; load b with memory contents
	bne  R1253	    ; branch if not equal (not zero)
	cmpa AMTEMP_StartTempToSelectHotOrColdAMTimer	 ; compare a with memory contents (data is cd)
	bcs  L1252	    ; branch if lower
	ldab Timer_O2CNTR_CountdownFromAbove196FtoEnableClosedLoop    ; load b with memory contents
	beq  R1253	    ; branch if equal (zero)
	decb		
	stab Timer_O2CNTR_CountdownFromAbove196FtoEnableClosedLoop    ; store b into memory
	rts		    ; return from subroutine

L1252:	bne  R1253	    ; branch if not equal (not zero)
	ldaa CoolantTemp    ; load a with memory contents
	ldx  #AMTPSW_TempPointToEnableSelectedAMTimer	 ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Timer_O2CNTR_CountdownFromAbove196FtoEnableClosedLoop    ; store a into memory
R1253:	rts		    ; return from subroutine


    ;.org	0x98ac
DRBFunctionTable:
	.word	OutputErrorCodes	     ; test command 0x10
	.word	OutputErrorBits 	     ; test command 0x11
	.word	SetupHiSpeedDataTransfer     ; test command 0x12
	.word	SetupATM		     ; test command 0x13
	.word	SendDiagnosticDataToSCI      ; test command 0x14
	.word	DRB_Return		     ; test command 0x15 - this test has a special routine built in to the DRB code - this
	.word	SendECUIDToSCI		     ; test command 0x16 - this test returns the ECU ID
	.word	ClearErrorCodes 	     ; test command 0x17
	.word	DRB_Return		     ; test command 0x18
	.word	DRB_Return		     ; test command 0x19 - set min idle speed test...
	.word	SwitchTest		     ; test command 0x1A
	.word	InitByteModeDownload	     ; test command 0x1B - Not used in the '89 T1; maybe use this test for trim function Not used otherwise...
	.word	DRB_Return		     ; test command 0x1C - reset EMR (Emmision Maintenance Reminder)

	   ;.org	0x98c6
DRBSerialToggles:
; these affect only bit 4 & 5 of the DRBSerialMode variable
; they indicate how many bytes the main DRB functions from the table above use
; the protocol is:
; byte 1 - test command
; byte 2 - either sub-command or memory address, depending on the test
; byte 3 - memory address
	.byte	0x20 ; 2 bytes
	.byte	0x20 ; 2 bytes
	.byte	0x30 ; 3 bytes
	.byte	0x20 ; 2 bytes
	.byte	0x00 ; 1 byte
	.byte	0x20 ; 2 bytes
	.byte	0x20 ; 2 bytes
	.byte	0x20 ; 2 bytes
	.byte	0x00 ; 1 byte
	.byte	0x30 ; 3 bytes

    ;.org	0x98d0
ATMFunctionTable:
; these are the sub-tests under the "SetupATM" DRB test above
	.word	ATM_Return		     ; sub-test command 0x00
	.word	ATM_IgnitionCoil	     ; sub-test command 0x01
	.word	ATM_Return		     ; sub-test command 0x02
	.word	ATM_Return		     ; sub-test command 0x03
	.word	ATM_InjBank1		     ; sub-test command 0x04
	.word	ATM_InjBank2		     ; sub-test command 0x05
	.word	ATM_Return		     ; sub-test command 0x06
	.word	ATM_AISMotorOpenClose	     ; sub-test command 0x07
	.word	ATM_FanRelay		     ; sub-test command 0x08
	.word	ATM_ACClutchRelay	     ; sub-test command 0x09
	.word	ATM_ASDRelay		     ; sub-test command 0x0A
	.word	ATM_PurgeSolenoid	     ; sub-test command 0x0B
	.word	ATM_SCServoSolenoid	     ; sub-test command 0x0C
	.word	ATM_AlternatorField	     ; sub-test command 0x0D
	.word	ATM_Tachometer		     ; sub-test command 0x0E
	.word	ATM_PTUIndicator	     ; sub-test command 0x0F
	.word	ATM_EGRSolenoid	             ; sub-test command 0x10
	.word	ATM_WGSolenoid		     ; sub-test command 0x11
	.word	ATM_BaroSolenoid	     ; sub-test command 0x12
	.word	ATM_Return		     ; sub-test command 0x13
	.word	ATM_AllSolenoidsRelays	     ; sub-test command 0x14
	.word	ATM_Return		     ; sub-test command 0x15
	.word	ATM_Return		     ; sub-test command 0x16
	.word	ATM_Return		     ; sub-test command 0x17
	.word	ATM_Return		     ; sub-test command 0x18
	.word	ATM_Return		     ; sub-test command 0x19

;     .org	0x9904
DRBMemoryTable: ;
; this is the data available under the "SendDiagnosticDataToSCI" DRB test above
	.byte	0x71 ; AmbientAirTempVolts	  - sub-test command 0x01
	.byte	0x6C ; O2SensorValue		  - sub-test command 0x02
	.byte	0x00 ;				  - sub-test command 0x03
	.byte	0x00 ;				  - sub-test command 0x04
	.byte	0x6A ; CoolantTemp		  - sub-test command 0x05
	.byte	0x6E ; RawCoolantTempVolts	  - sub-test command 0x06
	.byte	0x67 ; TpsVolts 		  - sub-test command 0x07
	.byte	0x02 ; MINTHR_LowestSessionTPS	  - sub-test command 0x08
	.byte	0x70 ; KnockVolts		  - sub-test command 0x09
	.byte	0x6B ; BatteryVolts		  - sub-test command 0x0A
	.byte	0x63 ; MapValue 		  - sub-test command 0x0B
	.byte	0x95 ; DesiredNewAisPosition	  - sub-test command 0x0C
	.byte	0x00 ;				  - sub-test command 0x0D
	.byte	0x8b ; ValueFromAdaptiveMemory	  - sub-test command 0x0E
	.byte	0x0E ; BaroPressure		  - sub-test command 0x0F
	.byte	0x5D ; EngineRpm_HB		  - sub-test command 0x10
	.byte	0x5D ; EngineRpm_HB		  - sub-test command 0x11
	.byte	0x00 ;				  - sub-test command 0x12
	.byte	0x26 ; ErrorCodeUpdateKeyOnCount  - sub-test command 0x13
	.byte	0x00 ;				  - sub-test command 0x14
	.byte	0xA0 ; CalculatedSparkAdvance	  - sub-test command 0x15
	.byte	0xA2 ; Cylinder1Retard		  - sub-test command 0x16
        .byte   0xA1 ; Cylinder2Retard            - sub-test command 0x17
        .byte   0xA3 ; Cylinder3Retard            - sub-test command 0x18
	.byte	0xA4 ; Cylinder4Retard		  - sub-test command 0x19
	.byte	0xD8 ; BoostTarget		  - sub-test command 0x1A

    ;.org	0x991e
SwitchTestTable:
; these sub-test fall under the "SwitchTest" DRB test above
	.word	SendSwitchStateToSerial   ;	  - sub-test command 0x01
	.word	SendOutputStatusToSerial  ;	  - sub-test command 0x02
	.word	SendOutputStatusToSerial2 ;	  - sub-test command 0x03

    ;.org	0x9924
RealTimeDataTable:
; these also fall under the "SendDiagnosticDataToSCI" DRB test above
	.word	SCI_MAPVolts    ; MAP Sensor Volts    - sub-test command 0x40
	.word	SCI_Speed       ; Vehicle Speed	      - sub-test command 0x41
	.word	SCI_O2Volts     ; O2 Sensor Volts     - sub-test command 0x42
	.word	EndRealTimeData ; End Diagnostic Data - sub-test command 0x43

DRBIISerialCommunications_MM:
        jsr  CallAndReturn1    ; call subroutine --> don't need this anymore...
	jsr  BYTE_MODE_SERIAL_CODE_DOWNLOAD_ROUTINE    ; call subroutine for hi-speed logger mod and trim function setup
	ldab DRBSerialMode    ; load b with memory contents
	bitb #bbe_FastSerial | bbe_ByteMode	     ;	-11000000-
	bne  R1255	    ; branch if not equal (not zero)
	ldaa CPU_SerialBaudRate    ; load a with memory contents
	anda #0x37	    ; AND a with value -00110111-
	cmpa BAUDLO_DRBBaudRateLo	    ; compare a with value -00100010-
	beq  L1254	    ; branch if equal (zero)
	ldaa BAUDLO_DRBBaudRateLo	    ; load a with value -00100010-
	staa CPU_SerialBaudRate
	rts		    ; return from subroutine

L1254:	ldaa CPU_SerialStatus	 ; load a with memory contents
;	staa LEEEE	    ;  (data is ff) - I think this is an error on ChryCo's part. The '90+ code does not have this line...
	bita #0x0e	    ;  -00001110-
	beq  DRB_NoRxError    ; branch if equal (zero)
	ldaa CPU_SerialData	; load a with memory contents
	rts		    ; return from subroutine

DRB_NoRxError:
	bita #0x20	    ;  -00100000-
	bne  DRB_ChrRxd     ; branch if not equal (not zero)
	brset *DRBSerialMode, #bbe_bottom, DRB_Timeout	  ; branch if bit(s) set
	incb		
	stab DRBSerialMode    ; store b into memory
	rts		    ; return from subroutine

DRB_Timeout:
	brclr *DRBSerialMode, #bbe_TestType3 | bbe_TestType2, R1255    ; branch if bit(s) clear
	bclr *DRBSerialMode, #bbe_TestType3 | bbe_TestType2    ; clear bits
	clr  DRBPointer1    ; zero byte at memory location
	rts		    ; return from subroutine

DRB_ChrRxd:
	ldaa CPU_SerialData	; load a with memory contents
	staa CPU_SerialData 
	andb #bbe_top	       ;  -11110000-
	stab DRBSerialMode    ; store b into memory
	bitb #bbe_TestType3 | bbe_TestType2	     ;	-00110000-
	bne  DRB_StorePointer	 ; branch if not equal (not zero)
	staa DRBPointer1    ; store a into memory
	clr  DRBPointer2    ; zero byte at memory location
	cmpa #0x1c	    ; compare a with value -00011100-
	bhi  R1255	    ; branch if higher
	suba #0x13	    ;  -00010011-
	bcs  R1255	    ; branch if lower
	bne  DRB_SetModeVar    ; branch if not equal (not zero)
	ldab TimerOverflowsBetweenDistPulses	; load b with memory contents
	cmpb #0x28	    ;  -00101000-
	bls  DRB_SetModeVar    ; branch if lower or same
	ldab #0x02	    ; load b with value -00000010-
	stab KeyOnOrEngineRunningTime	 ; store b into memory
DRB_SetModeVar:
	tab		    ; b = a
	ldx  #DRBSerialToggles	  ; load index with value
	abx		    ; add b to index
	ldab 0x00,x	    ; load b with memory at index + value
	orab DRBSerialMode
	stab DRBSerialMode    ; store b into memory
	rts		    ; return from subroutine

DRB_StorePointer:
	bitb #0x20	    ;  -00100000-
	beq  DRB_SendMemLocToSCI    ; branch if equal (zero)
	staa DRBPointer2    ; store a into memory
	andb #~bbe_TestType3   ;  -11011111-
	stab DRBSerialMode    ; store b into memory
R1255:	rts		    ; return from subroutine

DRB_SendMemLocToSCI:
	andb #~bbe_TestType2	      ;  -11101111-
	stab DRBSerialMode    ; store b into memory
	ldab DRBPointer1    ; load b with memory contents
	cmpb #0x1c	    ;  -00011100-
	beq  DRB_ResetEMR    ; branch if equal (zero)
	tab		    ; b = a
	ldaa DRBPointer2    ; load a with memory contents
	xgDX		    ; exchange D and X
	ldaa 0x00,x	    ; load a with memory at index + value
	jmp  SerialOutput1a

DRB_ResetEMR:
	clr  DRBPointer1    ; zero byte at memory location
	ldab TimerOverflowsBetweenDistPulses	; load b with memory contents
	cmpb #0x28	    ;  -00101000-
	bcs  L1257	    ; branch if lower
	sei		    ; disable interrupts
	ldab BitFlags_52    ; load b with memory contents
	bitb #b52_DRBToggle1 | b52_DRBToggle2	       ;  -00000011-
	bne  L1256	    ; branch if not equal (not zero)
	bset *BitFlags_52, #b52_DRBToggle1    ; set bits
	cli		    ; enable interrupts
	staa DRBOffsetStored_LB    ; store a into memory
	ldab DRBPointer2    ; load b with memory contents
	stab DRBOffsetStored_HB    ; store b into memory
	ldaa #0xe2	    ; load a with value -11100010-
	jmp  SerialOutput1a

L1256:	cli		    ; enable interrupts
L1257:	jmp  SerialOutput1

DRBIIOuput_MM:
	ldaa DRBSerialMode    ; load a with memory contents
	bita #bbe_TestType3 | bbe_TestType2	    ;  -00110000-
	bne  R1255	    ; branch if bit 4 or bit 5 is set
	ldab DRBPointer1    ; load b with memory contents
	subb #0x10	    ;  -00010000-
	bcs  R1255	    ; branch if lower
	cmpb #0x0c	    ;  -00001100-
	bhi  R1255	    ; branch if higher
	ldx  #DRBFunctionTable	  ; load index with value
	lslb		
	abx		    ; add b to index
	ldx  0x00,x	
	jmp  0x00,x	    ; indexed jump

OutputErrorCodes:
	ldx  #BitFlags_1d    ; load index with value
	ldab DRBPointer2    ; load b with memory contents
	cmpb #0x07	    ;  -00000111-
	bhi  L1258	    ; branch if higher
	negb		
	addb #0x07	    ;  -00000111-
	inx		    ; increment index (x=x+1)
	abx		    ; add b to index
	inc  DRBPointer2
	ldaa 0x00,x	    ; load a with memory at index + value
	bne  L1261	    ; branch if not equal (not zero)
L1258:	clr  DRBPointer1    ; zero byte at memory location
	ldaa #0xfe	    ; load a with value -11111110-
	jsr  SerialOutput1a    ; call subroutine
	adda #0x10	    ;  -00010000-
L1259:	inx		    ; increment index (x=x+1)
	cpx  #ErrorBitRegisterStored3	 ;  -00000000 00100101-
	bhi  L1261	    ; branch if higher
	adda 0x00,x	
	bra  L1259	    ; branch

OutputErrorBits:
	ldaa ErrorBitsAssociatedWithPIA1AndReg1eTo25_HB    ; load a with memory contents
	brclr *DRBPointer2, #$%11111111, L1260	  ; branch if bit(s) clear
	ldaa ErrorBitsAssociatedWithPIA1AndReg1eTo25_LB    ; load a with memory contents
	clr  DRBPointer1    ; zero byte at memory location
L1260:	inc  DRBPointer2
L1261:	jmp  SerialOutput1a

SetupHiSpeedDataTransfer:
	bset *DRBSerialMode, #bbe_FastSerial	; set bits
	clr  DRBPointer1    ; zero byte at memory location
L1262:	ldaa CPU_SerialStatus	 ; load a with memory contents
	bita #0x40	    ;  -01000000-
	beq  L1262	    ; branch if equal (zero)
	ldaa BAUDHI_DRBBaudRateHi	    ; load a with value -00000001-
	staa CPU_SerialBaudRate
DRB_Return:  
	rts		    ; return from subroutine

SetupATM:
	ldab TimerOverflowsBetweenDistPulses	; load b with memory contents
	cmpb #0x28	    ;  -00101000-
	bls  L1264	    ; branch if lower or same
	brset *BitFlags_55, #b55_O2Enable, L1264    ; branch if bit(s) set
	ldaa DRBPointer2    ; load a with memory contents
	cmpa #0x19	    ; compare a with value -00011001-
	bls  L1265	    ; branch if lower or same
L1264:	bclr *BitFlags_55, #b55_O2Enable    ; clear bits
	clra		    ; a = 0
	staa DRBPointer1    ; store a into memory
	jmp  SerialOutput1

L1265:	staa ATMOffset	    ; store a into memory
	tab		    ; b = a
	ldx  #ATMFunctionTable	  ; load index with value
	lslb		
	abx		    ; add b to index
	ldx  0x00,x	
	cpx  #ATM_Return    ;  -10011011 11010111-
	bne  L1261	    ; branch if not equal (not zero)
	jmp  SerialOutput1

SendDiagnosticDataToSCI:
	ldab DRBPointer2    ; load b with memory contents
	beq  L1266	    ; branch if equal (zero)
	cmpb #0x40	    ;  -01000000-
	bcc  SendRealTImeDatatoSCI    ; branch if greater or equal
	cmpb #0x1a	    ;  -00011010-
	bhi  L1266	    ; branch if higher
	cmpb #0x10	    ;  -00010000-
	bne  SendMemoryLocToSCI    ; branch if not equal (not zero)
	brclr *BitFlags_4f, #b4f_OffIdle, SendMemoryLocToSCI	; branch if bit(s) clear
L1266:	clra		    ; a = 0
	staa DRBPointer1    ; store a into memory
	rts		    ; return from subroutine

SendMemoryLocToSCI:
	ldx  #DRBMemoryTable-1	    ; load index with value
	abx		    ; add b to index
	ldab 0x00,x	    ; load b with memory at index + value
	beq  L1266	    ; branch if equal (zero)
	clra		    ; a = 0
	xgDX		    ; exchange D and X
	ldaa 0x00,x	    ; load a with memory at index + value
	jmp  SerialOutput1a

SendRealTImeDatatoSCI:
	subb #0x40	    ;  -01000000-
	cmpb #0x03	    ;  -00000011-
	bhi  L1266	    ; branch if higher
	ldx  #RealTimeDataTable    ; load index with value
	lslb		
	abx		    ; add b to index
	ldx  0x00,x	
	jmp  0x00,x	    ; indexed jump

SCI_MAPVolts:
	sei		    ; disable interrupts
	ldaa #0x10	    ; load a with value -00010000-
	staa CPU_A2DControlReg
	ldaa #0x07	    ; load a with value -00000111-
L1267:	deca		    ; decrement a
	bne  L1267	    ; branch if not equal (not zero)
	ldaa CPU_A2DResults1	; load a with memory contents
	cli		    ; enable interrupts
	bra  SerialOutput1a    ; branch

SCI_Speed:
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	bcc  SerialOutput1a    ; branch if greater or equal
	ldaa #0xff	    ; load a with value -11111111-
	bra  SerialOutput1a    ; branch

SCI_O2Volts:
	ldab O2SensorValue    ; load b with memory contents
	ldaa #0xff	    ; load a with value -11111111-
	cmpb O2MIDH_HighLimitForInMiddleDetermination	 ; compare b with memory contents (data is 1c)
	bhi  L1268	    ; branch if higher
	cmpb O2MIDL_LowLimitForInMiddleDetermination	; compare b with memory contents (data is 12)
	bhi  SerialOutput1a    ; branch if higher
	anda #0xa0	    ; AND a with value -10100000-
L1268:	anda #0xb1	    ; AND a with value -10110001-
	bra  SerialOutput1a    ; branch

EndRealTimeData:
	clra		    ; a = 0
	staa DRBPointer1    ; store a into memory
	brset *BitFlags_4f, #b4f_OffIdle, SerialOutput1a    ; branch if bit(s) set
	brset *BitFlags_54, #b54_FuelEngineNotRunning, SerialOutput1a	 ; branch if bit(s) set
	staa Timer_BaroReadInterval    ; store a into memory
	bclr *BitFlags_51, #b51_BaroSolEnergized    ; clear bits
	bset *BitFlags_51, #b51_SparkEngineNotRunning	 ; set bits
	bclr *BitFlags_2d, #b2d_ReadBaroRequired    ; clear bits
	ldaa #0xe3	    ; load a with value -11100011-
	bra  SerialOutput1a    ; branch

SendECUIDToSCI:
	ldx  #ENDIT1_PNPrefix	 ; load index with value
	ldab DRBPointer2    ; load b with memory contents
	bpl  L1269	    ; branch if plus (hi bit 0)
	lslb		
	lslb		
	stab DRBPointer2    ; store b into memory
L1269:	abx		    ; add b to index
	ldaa 0x00,x	    ; load a with memory at index + value
	inc  DRBPointer2
	brclr *DRBPointer2, #$%00000011, L1270	  ; branch if bit(s) clear
	bra  SerialOutput1a    ; branch

L1270:	bsr  SerialOutput1a    ; call subroutine
	adda #0x16	    ;  -00010110-
	dex		    ; decrement index (x=x-1)
	adda 0x00,x	
	dex		    ; decrement index (x=x-1)
	adda 0x00,x	
	dex		    ; decrement index (x=x-1)
	adda 0x00,x	
	ldab DRBPointer2    ; load b with memory contents
	subb #0x04	    ;  -00000100-
	lsrb		    ; logical shift right b
	lsrb		    ; logical shift right b
	orab #0x80	    ;  -10000000-
	aba		    ; a=a+b
	clr  DRBPointer1    ; zero byte at memory location
	bra  SerialOutput1a    ; branch

SerialOutput1:
	clra		    ; a = 0
SerialOutput1a:
	ldab CPU_SerialStatus	 ; load b with memory contents
	bpl  SerialOutput1a    ; branch if plus (hi bit 0)
	staa CPU_SerialData 
	rts		    ; return from subroutine

ClearErrorCodes:
	clr  DRBPointer1    ; zero byte at memory location
	ldab TimerOverflowsBetweenDistPulses	; load b with memory contents
	cmpb #0x28	    ;  -00101000-
	bhi  L1271	    ; branch if higher
	clr  BitFlags_4e    ; zero byte at memory location
	bra  SerialOutput1    ; branch

L1271:	ldaa BitFlags_4e    ; load a with memory contents
	inca		    ; increment a
	cmpa #0x18	    ; compare a with value -00011000-
	bls  L1272	    ; branch if lower or same
	clra		    ; a = 0
	staa BitFlags_4e    ; store a into memory
	bsr  ERASE_ERROR_CODES	  ; call subroutine
	ldaa #0xe0	    ; load a with value -11100000-
	bsr  SerialOutput1a    ; call subroutine
	bsr  SerialOutput1a    ; call subroutine
	bra  SerialOutput1a    ; branch

L1272:	staa BitFlags_4e    ; store a into memory
	ldaa #0xff	    ; load a with value -11111111-
	bra  SerialOutput1a    ; branch

SwitchTest:
	ldab DRBPointer2    ; load b with memory contents
	beq  R1273	    ; branch if equal (zero)
	cmpb #0x03	    ;  -00000011-
	bhi  R1273	    ; branch if higher
	ldx  #SwitchTestTable-2	    ; load index with value
	lslb
	abx		    ; add b to index
	ldx  0x00,x	
	jmp  0x00,x	    ; indexed jump

SendSwitchStateToSerial:
	ldaa StartupSwitchMirror2    ; load a with memory contents
	bra  SerialOutput1a    ; branch

SendOutputStatusToSerial:
	ldaa PIA1_PortA_DataDirection	 ; load a with memory contents
	bra  SerialOutput1a    ; branch

SendOutputStatusToSerial2:
	ldaa PIA1_PortB_DataDirection	 ; load a with memory contents
	bra  SerialOutput1a    ; branch

InitByteModeDownload:
	bset *DRBSerialMode, #bbe_ByteMode    ; set bits
	clr  DRBPointer1    ; zero byte at memory location
R1273:	rts		    ; return from subroutine

ERASE_ERROR_CODES:
	clra		    ; a = 0
	clrb		    ; b = 0
	stD *ErrorBitRegister0	  ; store D to RAM
	stD *ErrorBitRegister2	  ; store D to RAM
	stD *ErrorBitRegisterStored0	; store D to RAM
	stD *ErrorBitRegisterStored2	; store D to RAM
	staa b45_IPL1    ; store a into memory
	staa b46_IPL2    ; store a into memory
	staa ErrorCodeUpdateKeyOnCount	  ; store a into memory
	ldaa LB620	    ; load a with memory contents (data is ff)
	inca		    ; increment a
	beq  R1273	    ; branch if equal (zero)
	ldx  #0xb620	    ; load index with value
	bsr  L1274	    ; call subroutine
	ldx  #0xb630	    ; load index with value
	bsr  L1274	    ; call subroutine
	ldx  #0xb640	    ; load index with value
	bsr  L1274	    ; call subroutine
	ldx  #0xb650	    ; load index with value
L1274:	brset  0, X, #$%11111111, R1273    ; branch if bit(s) set
	ldaa #0x0e	    ; load a with value -00001110-
	staa CPU_EEPROMControlReg
	stab 0x00,x	
	inca		    ; increment a
	staa CPU_EEPROMControlReg
	ldx  #0x1a0a	    ; load index with value
L1275:	dex		    ; decrement index (x=x-1)
	bne  L1275	    ; branch if not equal (not zero)
	deca		    ; decrement a
	staa CPU_EEPROMControlReg
	clr  CPU_EEPROMControlReg    ; zero byte at memory location
	jmp  ResetCopTimer

ActuatorTestMode_MM:
	ldaa ATMOffset	    ; load a with memory contents
	beq  ATM_Return     ; branch if equal (zero)
	ldaa KeyOnOrEngineRunningTime	 ; load a with memory contents
	cmpa #0x96	    ; compare a with value -10010110-
	bcs  L1277	    ; branch if lower
	clrb		    ; b = 0
	ldaa DRBPointer1    ; load a with memory contents
	cmpa #0x13	    ; compare a with value -00010011-
	bne  L1276	    ; branch if not equal (not zero)
	stab DRBPointer1    ; store b into memory
L1276:	stab ATMOffset	    ; store b into memory
ATM_Return:
	rts		    ; return from subroutine

L1277:	ldaa PIA1_A_Buffer    ; load a with memory contents
	ldx  #ATMFunctionTable	  ; load index with value
	ldab ATMOffset	    ; load b with memory contents
	lslb		
	abx		    ; add b to index
	ldx  0x00,x	
	jmp  0x00,x	    ; indexed jump

ATM_FanRelay:
	anda #~pia1abuf_FanRelay	  ; AND a with value -11101111-
	brclr *Counter_MainLoop, #$%01111110, ATM_SetOutputBits    ; branch if bit(s) clear
	oraa #0x10	    ;  -00010000-
	bra  ATM_SetOutputBits	  ; branch

ATM_ASDRelay:
	ldab CPU_TimerControlReg1    ; load b with memory contents
	andb #0x3e	    ;  -00111110-
	stab CPU_TimerControlReg1    ; store b into memory
	ldab #0x08	    ; load b with value -00001000-
	stab CPU_TimerForceCompare    ; store b into memory
	oraa #pia1abuf_ASDRelay 	 ;  -00100000-
	brset *Counter_MainLoop, #bit_bit7, ATM_SetOutputBits	  ; branch if bit(s) set
	anda #~pia1abuf_ASDRelay	  ; AND a with value -11011111-
	bra  ATM_SetOutputBits	  ; branch

ATM_ACClutchRelay:
	oraa #pia1abuf_ACRelay		;  -00001000-
	ldab CONFIG_ConfigurationFlags	  ; load b with memory contents (data is 02)
	bitb #cfg_AC		;  -10000000-
	beq  L1278	    ; branch if equal (zero)
	anda #~pia1abuf_FanRelay	  ; AND a with value -11101111-
L1278:	brset *Counter_MainLoop, #bit_bit7, ATM_SetOutputBits	  ; branch if bit(s) set
	anda #~pia1abuf_ACRelay 	 ; AND a with value -11110111-
	bra  ATM_SetOutputBits	  ; branch

ATM_PurgeSolenoid:
	oraa #pia1abuf_PurgeSolenoid	      ;  -00000010-
	brset *Counter_MainLoop, #bit_bit7, ATM_SetOutputBits	  ; branch if bit(s) set
	anda #~pia1abuf_PurgeSolenoid	       ; AND a with value -11111101-
	bra  ATM_SetOutputBits	  ; branch

ATM_PTUIndicator:
	oraa #pia1abuf_PartThrotUnlock		;  -00000100-
	brset *Counter_MainLoop, #bit_bit7, ATM_SetOutputBits	  ; branch if bit(s) set
	anda #~pia1abuf_PartThrotUnlock 	 ; AND a with value -11111011-
ATM_SetOutputBits:
	staa PIA1_A_Buffer    ; store a into memory
	rts		    ; return from subroutine

ATM_SCServoSolenoid:
	oraa #pia1abuf_CruiseVent | pia1abuf_CruiseVacuum	   ;  -10000001-
	ldab Counter_MainLoop	  ; load b with memory contents
	cmpb #0x55	    ;  -01010101-
	bcs  ATM_SetOutputBits	  ; branch if lower
	anda #~(pia1abuf_CruiseVent | pia1abuf_CruiseVacuum)	  ; AND a with value -01111110-
	cmpb #0xaa	    ;  -10101010-
	bcs  ATM_SetOutputBits	  ; branch if lower
	oraa #pia1abuf_CruiseVacuum	     ;	-00000001-
	bra  ATM_SetOutputBits	  ; branch

ATM_EGRSolenoid:
	ldaa BitFlags_2d    ; load a with memory contents
	anda #~b2d_EGR     ; AND a with value -01111111-
	brset *Counter_MainLoop, #bit_bit7, L1280    ; branch if bit(s) set
	oraa #b2d_EGR	    ;  -10000000-
	bra  L1280	    ; branch

ATM_WGSolenoid:
	clra		    ; a = 0
	brset *Counter_MainLoop, #bit_bit7, L1279    ; branch if bit(s) set
	ldaa #0xc8	    ; load a with value -11001000-
L1279:	staa CurrentWastegateDutyCycle	 ; store a into memory
	rts		    ; return from subroutine

ATM_BaroSolenoid:
	ldaa BitFlags_2d    ; load a with memory contents
	anda #~b2d_ReadBaroRequired	     ; AND a with value -11011111-
	brset *Counter_MainLoop, #bit_bit7, L1280    ; branch if bit(s) set
	oraa #b2d_ReadBaroRequired	    ;  -00100000-
L1280:	staa BitFlags_2d    ; store a into memory
	rts		    ; return from subroutine

ATM_AllSolenoidsRelays:
	ldab CPU_TimerControlReg1    ; load b with memory contents
	andb #0x3e	    ;  -00111110-
	stab CPU_TimerControlReg1    ; store b into memory
	ldab #0x08	    ; load b with value -00001000-
	stab CPU_TimerForceCompare    ; store b into memory
	ldab #0x10	    ; load b with value -00010000-
	anda #0x48	    ; AND a with value -01001000-
	brset *Counter_MainLoop, #bit_bit7, L1281    ; branch if bit(s) set
	oraa #0xb7	    ;  -10110111-
	ldab #0x70	    ; load b with value -01110000-
L1281:	stab DesiredNewAisPosition    ; store b into memory
	staa PIA1_A_Buffer    ; store a into memory
	ldaa BitFlags_2d    ; load a with memory contents
	oraa #b2d_EGR | b2d_ReadBaroRequired	       ;  -10100000-
	ldab #0xc8	    ; load b with value -11001000-
	brset *Counter_MainLoop, #bit_bit7, L1282    ; branch if bit(s) set
	anda #~(b2d_EGR | b2d_ReadBaroRequired)		; AND a with value -01011111-
	clrb		    ; b = 0
L1282:	staa BitFlags_2d    ; store a into memory
	stab CurrentWastegateDutyCycle	 ; store b into memory
ATM_AlternatorField:
	ldaa PIA2_PortB_DataDirection	 ; load a with memory contents
	anda #~pia2b_AlternatorField	    ; AND a with value -11101111-
	brclr *Counter_MainLoop, #bit_bit7, L1283    ; branch if bit(s) clear
	oraa #pia2b_AlternatorField	    ;  -00010000-
L1283:	staa PIA2_PortB_DataDirection
	rts		    ; return from subroutine

ATM_Tachometer:
	ldaa PIA2_PortA_DataDirection	 ; load a with memory contents
	eora #pia2a_Tach	    ; XOR a with value -00000100-
	staa PIA2_PortA_DataDirection
	rts		    ; return from subroutine

ATM_AISMotorOpenClose:
	ldaa #0x10	    ; load a with value -00010000-
	brset *Counter_MainLoop, #bit_bit7, L1284    ; branch if bit(s) set
	ldaa #0x70	    ; load a with value -01110000-
L1284:	staa DesiredNewAisPosition    ; store a into memory
	rts		    ; return from subroutine

ATM_IgnitionCoil:
	bclr *PIA1_A_Buffer, #pia1abuf_ASDRelay    ; clear bits
	ldab Counter_MainLoop	  ; load b with memory contents
	lslb		
	bne  R1285	    ; branch if not equal (not zero)
	sei		    ; disable interrupts
	ldaa CPU_TimerControlReg1    ; load a with memory contents
	oraa #0x03	    ;  configure OC5 to set on successful compare
	staa CPU_TimerControlReg1
	ldab #0x08	    ;  force OC5 compare
	stab CPU_TimerForceCompare
	ldd  CPU_TimerCounterRegHigh
	addd #0x06d6	    ;  1.75ms coil charge time
	std  CPU_Timer_OC5_Dwell
	ldaa CPU_TimerControlReg1    ; load a with memory contents
	anda #0x3e	    ; configure OC5 to clear on successful compare, OC2 (WG) unaffected by compare
	staa CPU_TimerControlReg1
	cli		    ; enable interrupts
R1285:	rts		    ; return from subroutine

ATM_InjBank1:
	ldaa #0x3b	    ; load a with value -00111011-
	bra  L1286	    ; branch

ATM_InjBank2:
	ldaa #0x2f	    ; load a with value -00101111-
L1286:	bclr *PIA1_A_Buffer, #pia1abuf_ASDRelay    ; clear bits
	ldab Counter_MainLoop	  ; load b with memory contents
	lslb		
	bne  R1287	    ; branch if not equal (not zero)
	sei		    ; disable interrupts
	anda CPU_TimerControlReg1
	staa CPU_TimerControlReg1
	ldab #0x30	    ; load b with value -00110000-
	stab CPU_TimerForceCompare    ; store b into memory
	ldd  CPU_TimerCounterRegHigh
	addd #0x00fa	     ;	0.25ms
	std  CPU_Timer_OC3_InjectorBDriver
	std  CPU_Timer_OC4_InjectorADriver
	ldaa CPU_TimerControlReg1    ; load a with memory contents
	oraa #0x3c	    ;  -00111100-
	staa CPU_TimerControlReg1
	cli		    ; enable interrupts
R1287:	rts		    ; return from subroutine

CaculateChecksum:
	ldx  #ENDIT1_PNPrefix	 ; load index with value
	ldd  #0x9200	    ; load d (a&b) with value -10010010 00000000-
	stD *Temp0	    ; store D to RAM
	clra		    ; a = 0
L1288:	ldab #0x08	    ; load b with value -00001000-
	cpx  #0xB600	     ;	-10110110 00000000-
	bne  L1289	    ; branch if not equal (not zero)
	inc  Temp0
	inc  Temp0	
	ldx  #0xB800	; load index with value
L1289:	adda 0x00,x
	adda 0x01,x	
	adda 0x02,x	
	adda 0x03,x	
	adda 0x04,x	
	adda 0x05,x	
	adda 0x06,x	
	adda 0x07,x	
	abx		    ; add b to index
	cpx  Temp0	
	bne  L1289	    ; branch if not equal (not zero)
	brclr *Temp0, #$%11111111, L1290    ; branch if bit(s) clear
	psha		    ; push a onto stack
	jsr  ResetCopTimer    ; call subroutine
	ldaa #0x12	    ; load a with value -00010010-
	adda Temp0	
	staa Temp0	    ; store a into memory
	pula		    ; pull a from stack
	bra  L1288	    ; branch

L1290:	cmpa ENDITM_ECUID+1    ; compare a with memory contents (data is ff)
	bne  L1291	    ; branch if not equal (not zero)
	rts		    ; return from subroutine

L1291:	ldd  #0x0201	    ; load d (a&b) with value -00000010 00000001-
	jmp  ThrowNonCriticalError

FlashCodesOutOnCEL:
	ldaa Counter_MainLoop	  ; load a with memory contents
	lsla		    ; logical shift left a
	lsla		    ; logical shift left a
	bne  R1299	    ; branch if not equal (not zero)
	ldaa LastDistributorFallingEdgeTime    ; load a with memory contents
	bita #0x70	    ;  -01110000-
	beq  L1292	    ; branch if equal (zero)
	suba #0x10	    ;  -00010000-
	bita #0x70	    ;  -01110000-
	bne  L1298	    ; branch if not equal (not zero)
L1292:	ldab PIA1_A_Buffer    ; load b with memory contents
	eorb #pia1abuf_CELight		;  -01000000-
	stab PIA1_A_Buffer    ; store b into memory
	bita #0x0f	    ;  -00001111-
	beq  L1293	    ; branch if equal (zero)
	deca		    ; decrement a
	bita #0x0f	    ;  -00001111-
	beq  L1293	    ; branch if equal (zero)
	oraa #0x10	    ;  -00010000-
	bra  L1298	    ; branch

L1293:	tsta		    ; test a
	bmi  L1300	    ; branch if minus(hi bit 1)
	ldaa #0xaa	    ; load a with value -10101010-
	ldab DRBPointer2    ; load b with memory contents
	cmpb #0xfe	    ;  -11111110-
	beq  L1296	    ; branch if equal (zero)
	tstb		
	bmi  L1298	    ; branch if minus(hi bit 1)
	cmpb #0x08	    ;  -00001000-
	bcs  L1294	    ; branch if lower
	ldx  #0xb618	    ; load index with value
	abx		    ; add b to index
	brset  0, X, #$%11111111, L1306    ; branch if bit(s) set
	bra  L1295	    ; branch

L1294:	negb
	addb #0x07	    ;  -00000111-
	ldx  #ErrorBitRegister0    ; load index with value
	abx		    ; add b to index
L1295:	ldab 0x00,x	    ; load b with memory at index + value
	beq  L1298	    ; branch if equal (zero)
	bra  L1297	    ; branch

L1296:	clrb		    ; b = 0
L1297:	ldx  #ErrorCodesToDash_Table	    ; load index with value
	abx		    ; add b to index
	ldaa 0x00,x	    ; load a with memory at index + value
	anda #0x0f	    ; AND a with value -00001111-
	lsla		    ; logical shift left a
	oraa #0xa0	    ;  -10100000-
L1298:	staa LastDistributorFallingEdgeTime    ; store a into memory
R1299:	rts		    ; return from subroutine

L1300:	ldab DRBPointer2    ; load b with memory contents
	cmpb #0xff	    ;  -11111111-
	bne  L1301	    ; branch if not equal (not zero)
	ldaa ErrorCodeUpdateKeyOnCount	  ; load a with memory contents
	cmpa #0xb2	    ; compare a with value -10110010-
	bcc  L1301	    ; branch if greater or equal
	decb		
	stab DRBPointer2    ; store b into memory
	clrb		    ; b = 0
	bra  L1305	    ; branch

L1301:	cmpb #0xfe	    ;  -11111110-
	bne  L1302	    ; branch if not equal (not zero)
	incb		
L1302:	incb
	stab DRBPointer2    ; store b into memory
	cmpb #0x08	    ;  -00001000-
	bcs  L1303	    ; branch if lower
	brset *DRBPointer2, #bit_bit7, L1307	; branch if bit(s) set
	ldx  #0xb618	    ; load index with value
	abx		    ; add b to index
	brset  0, X, #$%11111111, L1306    ; branch if bit(s) set
	bra  L1304	    ; branch

L1303:	negb
	addb #0x07	    ;  -00000111-
	ldx  #ErrorBitRegister0    ; load index with value
	abx		    ; add b to index
L1304:	ldab 0x00,x	    ; load b with memory at index + value
	beq  L1306	    ; branch if equal (zero)
L1305:	ldx  #ErrorCodesToDash_Table	    ; load index with value
	abx		    ; add b to index
	ldaa 0x00,x	    ; load a with memory at index + value
	lsra		
	lsra		
	lsra		
	lsra		
	lsla		    ; logical shift left a
	oraa #0x40	    ;  -01000000-
	bra  L1298	    ; branch

L1306:	bset *DRBPointer2, #bit_bit7	; set bits
	ldaa #0x4a	    ; load a with value -01001010-
	bra  L1298	    ; branch

L1307:	clra		    ; a = 0
	staa DRBPointer1    ; store a into memory
	staa DRBPointer2    ; store a into memory
	rts		    ; return from subroutine


		;.org	0x9e08
ErrorCodesToDash_Table:
	.byte	0x12, 0x54, 0x53, 0x52, 0x51, 0x47, 0x46, 0x45, 0x44, 0x43
	.byte	0x42, 0x41, 0x37, 0x36, 0x35, 0x34, 0x33, 0x32, 0x31, 0x27
        .byte	0x27, 0x27, 0x26, 0x26, 0x26, 0x25, 0x24, 0x24, 0x23, 0x23
	.byte	0x22, 0x22, 0x21, 0x17, 0x16, 0x15, 0x14, 0x14, 0x13, 0x13
	.byte	0x11, 0x43, 0x43, 0x43, 0x42, 0x52, 0x32, 0x61, 0x62, 0x63

PIA1AManipulation_Table:
	.byte	0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0xFF, 0x12
	.byte	0x0C, 0x10, 0x0E, 0x0A, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF
	.byte	0xFF

ErrorBitManipulation_Table:
        .byte   0x2F, 0x0D, 0x11, 0x19, 0x20, 0x00, 0x01, 0x20, 0x00
	.byte	0x0B, 0x18, 0x00, 0xFF, 0x7F, 0x00, 0x14, 0x94, 0x08
	.byte	0x15, 0x94, 0x08, 0xFF, 0x7F, 0x00, 0x26, 0xA8, 0x80


DELAY_36USEC_ROUTINE:
	nop		    ; no operation
	nop		    ; no operation
	nop		    ; no operation
	nop		    ; no operation

Delay32uSec:
	ldY #0x0007         ; load Y index -00000000 00000111-
L1308:	deY		    ; decrement Y
	bne  L1308	    ; branch if not equal (not zero)
	rts		    ; return from subroutine

DRB_UpdatePIA1AndCheckOuputs_MM:
	clrb		    ; b = 0
	ldx  #CONFIG_ConfigurationFlags    ; load index with value
	brclr *PIA1_A_Buffer, #pia1abuf_ACRelay, L1310	  ; branch if bit(s) clear
	ldaa StartupSwitchMirror2    ; load a with memory contents
	bita #sw2_ACclutch	    ;  -00010000-
	brclr  0, X, #cfg_AC, L1309	 ; branch if bit(s) clear
	ldaa PIA1_A_Buffer    ; load a with memory contents
	bita #pia1abuf_FanRelay 	 ;  -00010000-
L1309:	beq  L1310	    ; branch if equal (zero)
	ldab #0x08	    ; load b with value -00001000-
L1310:	ldaa BatteryVolts    ; load a with memory contents
	cmpa #0xa2	    ; compare a with value -10100010-
	bcc  UPDATE_PIA1_A_PDR_DDR_REGISTER    ; branch if greater or equal
	ldab #0xff	    ; load b with value -11111111-
UPDATE_PIA1_A_PDR_DDR_REGISTER:
	ldaa PIA1_A_Buffer    ; load a with memory contents
	staa PIA1_PortA_DataDirection
	ldx  #PIA1_PortA_DataDirection	  ; load index with value
	bclr  1, X, #$%00000100    ; bit clear
	sei		    ; disable interrupts
	bset  0, X, #$%11111111    ; bit set
	bsr  DELAY_36USEC_ROUTINE    ; call subroutine
	stab 0x00,x
	cli		    ; enable interrupts
	bset  1, X, #$%00000100    ; bit set
	bsr  Delay32uSec    ; call subroutine
	eora PIA1_PortA_DataDirection
	ldx  #PIA1AManipulation_Table	    ; load index with value
	ldab Counter_MainLoop	  ; load b with memory contents
	andb #0x07	    ;  -00000111-
	abx		    ; add b to index
	anda 0x00,x	
	bita PIAMSK_PIA1ADDRMask	  ;  (data is 3a)
	beq  L1314	    ; branch if no bits are set
	cmpb #0x03	    ;  -00000011-
	bne  L1312	    ; branch if not equal (not zero)
	tst  CONFIG_ConfigurationFlags	  ;  (data is 02)
	bpl  L1311	    ; branch if plus (hi bit 0)
	brclr *PIA1_A_Buffer, #pia1abuf_FanRelay, L1312    ; branch if bit(s) clear
	bra  L1314	    ; branch

L1311:	brset *BitFlags_54, #b54_DisableNormalDwell, L1314    ; branch if bit(s) set
	ldaa KeyOnOrEngineRunningTime	 ; load a with memory contents
	cmpa #0x0b	    ; compare a with value -00001011-
	bcs  L1314	    ; branch if lower
	brset *StartupSwitchMirror2, #sw2_ACclutch, L1314    ; branch if bit(s) set
L1312:	ldaa CountdownTimerFromKeyOn	; load a with memory contents
	bne  L1314	    ; branch if not equal (not zero)
	ldab #0x20	    ; load b with value -00100000-
	ldaa 0x08,x	    ; load a with memory at index + value
	cmpa #0x12	    ; compare a with value -00010010-
	bne  L1313	    ; branch if not equal (not zero)
	jsr  ThrowCriticalError    ; call subroutine
	bcc  L1314	    ; branch if greater or equal
	bset *b46_IPL2, #b46_MajorFault    ; set bits
	bra  L1314	    ; branch

L1313:	jsr  ThrowNonCriticalError    ; call subroutine
L1314:	ldaa BitFlags_2d    ; load a with memory contents
	anda #b2d_EGR | b2d_ReadBaroRequired | b2d_EMR	  ; AND a with value -10110000-
	ldab #0x4f	    ; load b with value -01001111-
	sei		    ; disable interrupts
	andb PIA1_PortB_DataDirection
	stab Temp0	    ; store b into memory
	oraa Temp0	    ; OR a with memory contents
	staa PIA1_PortB_DataDirection
	ldx  #PIA1_PortB_DataDirection	  ; load index with value
	bclr  1, X, #$%00000100    ; bit clear
	bset  0, X, #$%10110000    ; bit set
	ldab BatteryVolts    ; load b with memory contents
	cmpb #0xa2	    ;  -10100010-
	bcs  L1315	    ; branch if lower
	jsr  Delay32uSec    ; call subroutine
	bclr  0, X, #$%10110000    ; bit clear
L1315:	cli		    ; enable interrupts
	bset  1, X, #$%00000100    ; bit set
	jsr  Delay32uSec    ; call subroutine
	ldx  #PIA1AManipulation_Table	    ; load index with value
	ldab Counter_MainLoop	  ; load b with memory contents
	andb #0x07	    ;  -00000111-
	abx		    ; add b to index
	ldaa #0x40	    ; load a with value -01000000-
	sei		    ; disable interrupts
	anda BitFlags_55    ; logical and a with memory contents
	ldab BitFlags_2d    ; load b with memory contents
	andb #~b2d_bit6 	 ;  -10111111-
	aba		    ; a=a+b
	eora PIA1_PortB_DataDirection
	cli		    ; enable interrupts
	anda 0x00,x	
	bita PIBMSK_PIA1BDDRMask	  ;  (data is e0)
	beq  R1318	    ; branch if equal (zero)
	ldaa CountdownTimerFromKeyOn	; load a with memory contents
	bne  R1318	    ; branch if not equal (not zero)
	ldaa 0x10,x	    ; load a with memory at index + value
	cmpa #0x0d	    ; compare a with value -00001101-
	bne  L1316	    ; branch if not equal (not zero)
	brset *b46_IPL2, #b46_WGSolFault, R1318	; branch if bit(s) set
	ldab #0xa0	    ; load b with value -10100000-
	bsr  ThrowNonCriticalError    ; call subroutine
	bcc  R1318	    ; branch if greater or equal
	bset *b46_IPL2, #b46_WGSolFault	; set bits
	rts		    ; return from subroutine

L1316:	ldab #0x20	    ; load b with value -00100000-
	cmpa #0x2f	    ; compare a with value -00101111-
	bne  L1319	    ; branch if not equal (not zero)
L1317:	bsr  ThrowCriticalError    ; call subroutine
	bcc  R1318	    ; branch if greater or equal
	bset *b46_IPL2, #b46_MajorFault    ; set bits
R1318:	rts		    ; return from subroutine

L1319:	cmpa #0x11	    ; compare a with value -00010001-
	bne  ThrowNonCriticalError    ; branch if not equal (not zero)
	ldx  #CONFIG_ConfigurationFlags    ; load index with value
	brset  0, X, #cfg_EGR, L1317	; branch if bit(s) set
	rts		    ; return from subroutine

ThrowCriticalError:
	ldx  #CONFIG_ConfigurationFlags    ; load index with value
	brclr  0, X, #cfg_EGR, ThrowNonCriticalError	; branch if bit(s) clear
	brset *b46_IPL2, #b46_MajorFault, ThrowNonCriticalError    ; branch if bit(s) set
	orab #0x80	    ;  -10000000-
ThrowNonCriticalError:
	ldx  #FLTMSK_ErrorBitsMask1    ; load index with value
L1320:	brclr  0, X, #$%11111111, L1321    ; branch if bit(s) clear
	cmpa 0x00,x	    ; compare a with memory at index + value
	beq  L1323	    ; branch if equal (zero)
	inx		    ; increment index (x=x+1)
	bra  L1320	    ; branch

L1321:	tstb
	bmi  L1324	    ; branch if minus(hi bit 1)
	cmpa ErrorBitRegisterStored3	; compare a with memory contents
	beq  L1322	    ; branch if equal (zero)
	cmpa ErrorBitRegisterStored2	; compare a with memory contents
	bne  L1324	    ; branch if not equal (not zero)
L1322:	clr  ErrorCodeUpdateKeyOnCount	  ; zero byte at memory location
L1323:	clra		    ; a = 0
	rts		    ; return from subroutine

L1324:	andb #0x7f	    ;  -01111111-
	cmpb #0x01	    ;  -00000001-
	beq  L1327	    ; branch if equal (zero)
	ldx  #ErrorBitsAssociatedWithPIA1AndReg1eTo25_HB    ; load index with value
	cmpa 0x00,x	    ; compare a with memory at index + value
	beq  L1325	    ; branch if equal (zero)
	inx		    ; increment index (x=x+1)
	cmpa 0x00,x	    ; compare a with memory at index + value
	beq  L1325	    ; branch if equal (zero)
	tst  0x00,x	
	beq  L1325	    ; branch if equal (zero)
	dex		    ; decrement index (x=x-1)
	tst  0x00,x	
	bne  L1323	    ; branch if not equal (not zero)
L1325:	staa 0x00,x
	inc  0x02,x	
	beq  L1326	    ; branch if equal (zero)
	cmpb 0x02,x	
	bcs  L1326	    ; branch if lower
	ldab 0x02,x	    ; load b with memory at index + value
	clc		    ; clear carry
	rts		    ; return from subroutine

L1326:	clr  0x00,x
	clr  0x02,x	
L1327:	ldx  #ErrorBitRegister0    ; load index with value
L1328:	cmpa 0x00,x	    ; compare a with memory at index + value
	bne  L1329	    ; branch if not equal (not zero)
	clr  0x00,x	
	bra  L1330	    ; branch

L1329:	inx		    ; increment index (x=x+1)
	cpx  #ErrorBitRegisterStored3	 ;  -00000000 00100101-
	bls  L1328	    ; branch if lower or same
L1330:	ldx  #ErrorBitRegisterStored3	 ; load index with value
L1331:	ldab 0x00,x	    ; load b with memory at index + value
	staa 0x00,x	
	tba		    ; a = b
	beq  L1334	    ; branch if equal (zero)
	dex		    ; decrement index (x=x-1)
	cpx  #ErrorBitRegister0    ;  -00000000 00011110-
	bcc  L1331	    ; branch if greater or equal
	sei		    ; disable interrupts
	ldab BitFlags_52    ; load b with memory contents
	bitb #b52_DRBToggle1 | b52_DRBToggle2	       ;  -00000011-
	bne  L1334	    ; branch if not equal (not zero)
	bset *BitFlags_52, #b52_DRBToggle1    ; set bits
	cli		    ; enable interrupts
	staa DRBOffsetStored_LB    ; store a into memory
	ldx  #0xb61f	    ; load index with value
L1332:	inx		    ; increment index (x=x+1)
	cpx  #0xb660	    ;  -10110110 01100000-
	beq  L1333	    ; branch if equal (zero)
	ldab 0x00,x	    ; load b with memory at index + value
	cba		
	beq  L1333	    ; branch if equal (zero)
	incb		
	bne  L1332	    ; branch if not equal (not zero)
	xgDX		    ; exchange D and X
	subd #0xB600	    ;  -10110110 00000000-
	stab DRBOffsetStored_HB    ; store b into memory
	bra  L1334	    ; branch

L1333:	bclr *BitFlags_52, #b52_DRBToggle1    ; clear bits
L1334:	cli		    ; enable interrupts
	clr  ErrorCodeUpdateKeyOnCount	  ; zero byte at memory location
	sec		    ; set carry
R1335:	rts		    ; return from subroutine

ProcessErrorBits_WorkWithData_MM:

	brclr *BitFlags_47, #bit_all, R1335    ; branch if bit(s) clear
	ldaa CountdownTimerFromKeyOn	; load a with memory contents
	bne  R1335	    ; branch if not equal (not zero)
	clra		    ; a = 0
	clrb		    ; b = 0
	sec		    ; set carry
L1336:	rola
	bcs  R1335	    ; branch if lower
	addb #0x03	    ;  -00000011-
	bita BitFlags_47
	beq  L1336	    ; branch if equal (zero)
	ldx  #ErrorBitManipulation_Table	    ; load index with value
	abx		    ; add b to index
	stD *Temp3	    ; store D to RAM
	coma		
	sei		    ; disable interrupts
	anda BitFlags_47    ; logical and a with memory contents
	staa BitFlags_47    ; store a into memory
	cli		    ; enable interrupts
	ldd  0x00,x	
	tstb		
	bpl  L1337	    ; branch if plus (hi bit 0)
	bset *Temp4, #bit_bit7	  ; set bits
L1337:	jsr  ThrowNonCriticalError    ; call subroutine
	brclr *Temp4, #bit_bit7, L1338	  ; branch if bit(s) clear
	bcc  L1338	    ; branch if greater or equal
	ldx  #ErrorBitManipulation_Table	    ; load index with value
	ldab Temp4	    ; load b with memory contents
	andb #0x7f	    ;  -01111111-
	abx		    ; add b to index
	ldaa 0x02,x	    ; load a with memory at index + value
	sei		    ; disable interrupts
	oraa b45_IPL1    ; OR a with memory contents
	staa b45_IPL1    ; store a into memory
	cli		    ; enable interrupts
L1338:	ldd  Temp3	    ; load d (a&b) with memory contents
	andb #0x7f	    ;  -01111111-
	clc		    ; clear carry
	bra  L1336	    ; branch

SimulateMapReadingFromTps:
	ldab EngineRpm_HB    ; load b with memory contents
	cmpb #0x7e	    ;  -01111110-
	ldaa #0x00	    ; load a with value -00000000-
	bcc  L1340	    ; branch if greater or equal
	subb #0x10	    ;  -00010000-
	bcc  L1339	    ; branch if greater or equal
	clrb		    ; b = 0
L1339:	ldaa #0x52	    ; load a with value -01010010-
	mul		    ; multiply (d=a*b)
	adca MINTHR_LowestSessionTPS
	tab		    ; b = a
	ldaa TpsVolts	    ; load a with memory contents
	adda THROFF_OffsetAddedToCalcThrottle	 ;  (data is 0b)
	sba		    ; subtract (a=a-b)
	bcc  L1340	    ; branch if greater or equal
	clra		    ; a = 0
L1340:	ldx  #LMPINN_LimpinTableForMapFromThrottle    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	adda MPLMOF_OffsetForCalcMapInMapLimpin    ;  (data is 20)
	rts		    ; return from subroutine

VerifyOperationOfBatteryVoltage_MM:
	ldaa BatteryVolts    ; load a with memory contents
	cmpa #0x41	    ; compare a with value -01000001-
	bcc  L1341	    ; branch if greater or equal
	brset *BitFlags_54, #b54_FuelEngineNotRunning, R2341	; branch if bit(s) set
	brset *b45_IPL1, #b45_Bad_BatVolts, R2341	; branch if bit(s) set
	ldd  KeyOnOrEngineRunningTime	 ; load d (a&b) with memory contents
	cmpa #0x15	    ; compare a with value -00010101-
	bcs  R2341	    ; branch if lower
	bitb #0x3f	    ;  -00111111-
	bne  R2341	    ; branch if not equal (not zero)
	ldd  #0x2290	    ; load d (a&b) with value -00100010 10010000-
	jsr  ThrowNonCriticalError    ; call subroutine
	bcc  R2341	    ; branch if greater or equal
	bset *b45_IPL1, #b45_Bad_BatVolts	; set bits
R2341:	rts		    ; return from subroutine

L1341:	brclr *b45_IPL1, #b45_Bad_BatVolts, R2341	; branch if bit(s) clear
	ldaa #0x05	    ; load a with value -00000101-
	jmp  ResetErrorCodeIfTimerExpired

CheckIfCheckEngineLightShouldBeOn_MM:
	ldab #pia1abuf_CELight	    ; load b with value -01000000-
	brclr *BitFlags_54, #b54_FuelEngineNotRunning, DetermineEngineRunningCELStatus	; branch if bit(s) clear
	ldaa DRBPointer1    ; load a with memory contents
	cmpa #0x0a	    ; compare a with value -00001010-
	bne  L1342	    ; branch if not equal (not zero)
	jmp  FlashCodesOutOnCEL

L1342:	cmpa #0x18	    ; compare a with value -00011000-
	bne  L1343	    ; branch if not equal (not zero)
	ldaa Counter_MainLoop	  ; load a with memory contents
	lsla		    ; logical shift left a
	bmi  TurnCheckEngineLightOnAndOff	 ; branch if minus(hi bit 1)
	bra  L1346	    ; branch

L1343:	ldaa KeyOnOrEngineRunningTime	 ; load a with memory contents
	bne  TurnCheckEngineLightOnAndOff	 ; branch if not equal (not zero)
	bra  L1346	    ; branch

DetermineEngineRunningCELStatus:	
        ldx  KeyOnOrEngineRunningTime
	cpx  #0x0003                     ;  -00000000 00000011-
	bls  TurnCheckEngineLightOnAndOff	 ; branch if lower or same
	brclr *PIA1_A_Buffer, #pia1abuf_CELight, R1347	  ; branch if bit(s) clear
	ldaa b45_IPL1    ; load a with memory contents
	bita IPLMSK_PowerLossLightMask	  ;  (data is fe)
	bne  L1346	    ; branch if not equal (not zero)
	ldx  #CONFIG_ConfigurationFlags    ; load index with value
	ldaa b46_IPL2    ; load a with memory contents
	bita #b46_InjectorFault 	 ;  -00010000-
	bne  L1346	    ; branch if not equal (not zero)
	brset  0, X, #cfg_EGR, L1345	; branch if bit(s) set
	anda #~(b46_bit7 | b46_MajorFault)	    ; AND a with value -00111111-
L1345:	bita IPLMSK2_PowerLossLightMask2    ;  (data is d8)
	beq  TurnCheckEngineLightOnAndOff	 ; branch if equal (zero)
L1346:	clrb		    ; b = 0
TurnCheckEngineLightOnAndOff:
	ldaa #~pia1abuf_CELight 	 ; load a with value -10111111-
	anda PIA1_A_Buffer    ; logical and a with memory contents
	aba		    ; a=a+b
	staa PIA1_A_Buffer    ; store a into memory
R1347:	rts		    ; return from subroutine

UpdateErrorTimersAndPossiblyClearErrors_MM:
	ldaa Counter_MainLoop	  ; load a with memory contents
	bne  L1351	    ; branch if not equal (not zero)
	ldd  ErrorBitsAssociatedWithPIA1AndReg1eTo25_HB    ; load d (a&b) with memory contents
	tsta		    ; test a
	beq  L1348	    ; branch if equal (zero)
	dec  ClearTheErrorTimer_0    ; decrement memory contents
	bne  L1348	    ; branch if not equal (not zero)
	clr  ErrorBitsAssociatedWithPIA1AndReg1eTo25_HB    ; zero byte at memory location
L1348:	tstb
	beq  L1349	    ; branch if equal (zero)
	dec  ClearTheErrorTimer_1    ; decrement memory contents
	bne  L1349	    ; branch if not equal (not zero)
	clr  ErrorBitsAssociatedWithPIA1AndReg1eTo25_LB    ; zero byte at memory location
L1349:	ldaa ERRORCODERESETTIMERIN_UN_ERRORCODEIN_LN_VAR    ; load a with memory contents
	beq  L1351	    ; branch if equal (zero)
	suba #0x10	    ;  -00010000-
	bita #0xf0	    ;  -11110000-
	bne  L1350	    ; branch if not equal (not zero)
	clra		    ; a = 0
L1350:	staa ERRORCODERESETTIMERIN_UN_ERRORCODEIN_LN_VAR    ; store a into memory
L1351:	ldaa BitFlags_54    ; load a with memory contents
	bita #b54_FuelEngineNotRunning | b54_NeedSetup		;  -10000001-
	bne  R1356	    ; branch if not equal (not zero)
	bset *BitFlags_54, #b54_NeedSetup    ; set bits
	ldaa ErrorCodeUpdateKeyOnCount	  ; load a with memory contents
	ldab ErrorBitRegisterStored3	; load b with memory contents
	beq  L1353	    ; branch if equal (zero)
	tsta		    ; test a
	bpl  L1352	    ; branch if plus (hi bit 0)
	clra		    ; a = 0
L1352:	inca		    ; increment a
	cmpa #0x32	    ; compare a with value -00110010-
	bls  L1355	    ; branch if lower or same
	ldaa CPU_EEPROMControlReg    ; load a with memory contents
	bne  R1356	    ; branch if not equal (not zero)
	jmp  ERASE_ERROR_CODES

L1353:	tsta		    ; test a
	bmi  L1354	    ; branch if minus(hi bit 1)
	ldaa #0x80	    ; load a with value -10000000-
L1354:	inca		    ; increment a
	beq  R1356	    ; branch if equal (zero)
L1355:	staa ErrorCodeUpdateKeyOnCount	  ; store a into memory
R1356:	rts		    ; return from subroutine

DetectAlternatorFault_MM:
	ldaa Counter_MainLoop	  ; load a with memory contents
	bita #0x1f	    ;  -00011111-
	bne  R1359	    ; this routine only runs every 341ms
	brset *BitFlags_54, #b54_FuelEngineNotRunning, R1359	; branch if bit(s) set
	ldaa BatteryVolts    ; load a with memory contents
	suba TargetBatteryVolts
	bcc  L1357	    ; branch if greater or equal
	bclr *b45_IPL1, #b45_BattNotCharging    ; clear bits
	ldab EngineRpm_HB    ; load b with memory contents
	cmpb BTLRPM_LowBatteryVoltageAtThisRpm1500    ; compare b with memory contents (data is 2e)
	bcs  R1359	    ; branch if lower
	nega		    ; negate a (set high bit)
	cmpa #0x10	    ; compare a with value -00010000-
	bcs  R1359	    ; branch if lower
	ldd  #0x0555	    ; load d (a&b) with value -00000101 01010101-
	jmp  ThrowNonCriticalError

L1357:	cmpa #0x10	    ; compare a with value -00010000-
	bcs  L1358	    ; branch if lower
	brset *b45_IPL1, #b45_BattNotCharging, R1359    ; branch if bit(s) set
	ldd  #0x06a0	    ; load d (a&b) with value -00000110 10100000-
	jsr  ThrowNonCriticalError    ; call subroutine
	bcc  R1359	    ; branch if greater or equal
	bset *b45_IPL1, #b45_BattNotCharging    ; set bits
	rts		    ; return from subroutine

L1358:	bclr *b45_IPL1, #b45_BattNotCharging    ; clear bits
R1359:	rts		    ; return from subroutine

CheckForErrorsAndSetCodes_MM:
	brset *BitFlags_54, #b54_FuelEngineNotRunning, R1363	; branch if bit(s) set
	ldaa CoolantTemp    ; load a with memory contents
	cmpa ERRTMP_CoolantTempLimitforErrorCodeSetting	    ; compare a with memory contents (data is a0)
	bcs  R1363	    ; branch if lower
L1360:	ldaa CONFIG_ConfigurationFlags	  ; load a with memory contents (data is 02)
	bita #cfg_ATX		;  -00100000-
	beq  L1361	    ; branch if equal (zero)
	brclr *BitFlags_AIS, #b0c_ATXInGear, R1363    ; branch if bit(s) clear
L1361:	ldd  KeyOnOrEngineRunningTime	 ; load d (a&b) with memory contents
	cmpa #0x0b	    ; compare a with value -00001011-
	bcs  R1363	    ; branch if lower
	bitb #0x1f	    ;  -00011111-
	bne  R1363	    ; branch if not equal (not zero)
	brset *StartupSwitchMirror2, #sw2_Brake, R1363    ; branch if bit(s) set
	brclr *BitFlags_4f, #b4f_OffIdle, R1363    ; branch if bit(s) clear
	ldaa EngineRpm_HB    ; load a with memory contents
	cmpa ERRRPM_RPMLimitforErrorCodeSetting	    ; compare a with memory contents (data is 38)
	bcs  R1363	    ; branch if lower
	ldaa BaroPressure    ; load a with memory contents
	suba MapValue	
	bcc  L1362	    ; branch if greater or equal
	clra		    ; a = 0
L1362:	cmpa ERRMAP_MAPLimitforErrorCodeSetting	    ; compare a with memory contents (data is 1c)
	bcc  R1363	    ; branch if greater or equal
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	cmpD #0x002A	     ; compare D -00000000 00101010-
	bcc  R1363	    ; branch if greater or equal
	ldd  #0x2320	    ; load d (a&b) with value -00100011 00100000-
	jsr  ThrowCriticalError    ; call subroutine
	bcc  R1363	    ; branch if greater or equal
	bset *b46_IPL2, #b46_MajorFault    ; set bits
R1363:	rts		    ; return from subroutine

ThrowMajorErrorIfRequired_MM:
	ldaa CONFIG_ConfigurationFlags	  ; load a with memory contents (data is 02)
	bita #cfg_EGR	       ;  -01000000-
	beq  L1366	    ; branch if equal (zero)
	ldaa ErrorBitRegisterStored3	; load a with memory contents
	cmpa #0x19	    ; compare a with value -00011001-
	bne  L1364	    ; branch if not equal (not zero)
	brclr *BitFlags_47, #b47_AisFail, L1364    ; branch if bit(s) clear
	ldd  #0x1920	    ; load d (a&b) with value -00011001 00100000-
	jsr  ThrowCriticalError    ; call subroutine
	bcs  L1365	    ; branch if lower
L1364:	brclr *BitFlags_50, #b50_BadO2, R1367	 ; branch if bit(s) clear
L1365:	bset *b46_IPL2, #b46_MajorFault    ; set bits
	rts		    ; return from subroutine

L1366:	bclr *b46_IPL2, #b46_bit7 | b46_MajorFault	 ; clear bits
R1367:	rts		    ; return from subroutine

VerifyOperationOfIgnitionCoilDriver_MM:
	ldaa CountdownTimerFromKeyOn	; load a with memory contents
	bne  R1368	    ; branch if not equal (not zero)
	ldaa BatteryVolts    ; load a with memory contents
	cmpa #0x93	    ; compare a with value -10010011-
	bcs  R1368	    ; branch if lower
	ldaa CPU_PortA		; load a with memory contents
	tab		    ; b = a
	lsra		
	lsra	; this lines up the ignition coil bit with the driver sense bit	
	eora PIA2_PortB_DataDirection
	eorb CPU_PortA	    
	bitb #CPU_PortA_IgnCoil	    ;  -00001000-
	bne  R1368	    ; branch if not equal (not zero)
	bita #pia2b_IgnCoilDriverSense	    ;  -00000010-
	bne  R1368	    ; branch if not equal (not zero)
	ldaa Counter_MainLoop	  ; load a with memory contents
	bita #0x03	    ;  -00000011-
	bne  R1368	    ; branch if not equal (not zero)
	ldd  #0x0910	    ; load d (a&b) with value -00001001 00010000-
	jmp  ThrowNonCriticalError

R1368:	rts		    ; return from subroutine

VerifyOperationOfFuelInjectorDrivers_MM:
	ldaa BatteryVolts    ; load a with memory contents
	cmpa #0xc3	    ; compare a with value -11000011-
	bcs  R1372	    ; branch if lower
	brclr *StartupSwitchMirror2, #sw2_B1Volt, R1372    ; branch if bit(s) clear
        ldaa CPU_TimerControlReg2    ; load a with memory contents
	bita #0x10	    ;  -00010000-
	bne  R1372	    ; branch if not equal (not zero)
	ldaa CPU_PortA		; load a with memory contents
	psha		    ; push a onto stack
	anda #CPU_PortA_InjectorB | CPU_PortA_InjectorA 	 ; AND a with value -00110000-
	cmpa #CPU_PortA_InjectorA	    ; compare a with value -00010000-
	beq  L1369	    ; branch if equal (zero)
	cmpa #CPU_PortA_InjectorB	    ; compare a with value -00100000-
	bne  L1371	    ; branch if not equal (not zero)
L1369:	ldd  CPU_TimerCounterRegHigh
	subd CPU_TimerInputCapture1_Distributor
	cmpD #0x02ee	    ; 0.75ms
	bcs  L1371	    ; branch if lower
	ldaa PIA2_PortB_DataDirection	 ; load a with memory contents
	bita #pia2b_InjectorDriverSense	    ;  -00000001-
	beq  L1371	    ; branch if equal (zero)
	pula		    ; pull a from stack
	tab		    ; b = a
	eora CPU_PortA
	bita #CPU_PortA_InjectorB | CPU_PortA_InjectorA 	  ;  -00110000-
	bne  R1372	    ; branch if not equal (not zero)
	brset *b46_IPL2, #b46_InjectorFault, R1372	 ; branch if bit(s) set
	ldaa #0x17	    ; load a with value -00010111-
	bitb #CPU_PortA_InjectorB	    ;  -00100000-
	beq  L1370	    ; branch if equal (zero)
	inca		    ; increment a
L1370:	ldab #0x90	    ; load b with value -10010000-
	jsr  ThrowNonCriticalError    ; call subroutine
	bcc  R1372	    ; branch if greater or equal
	bset *b46_IPL2, #b46_InjectorFault	 ; set bits
	rts		    ; return from subroutine

L1371:	pula		    ; pull a from stack
R1372:	rts		    ; return from subroutine

CheckIfMapSensorHasStartedWorkingAgain:
	ldaa TimerOverflowsBetweenDistPulses	; load a with memory contents
	cmpa #0x28	    ; compare a with value -00101000-
	bcs  L1375	    ; branch if lower
	ldaa CPU_A2DResults1	; load a with memory contents
	brclr *Counter_MainLoop, #$%01111111, L1373	; branch if bit(s) clear
	cmpa MapVolts	    ; compare a with memory contents
	bcs  L1374	    ; branch if lower
	cmpa MapValue	    ; compare a with memory contents
	bls  L1375	    ; branch if lower or same
	staa MapValue	    ; store a into memory
	bra  L1375	    ; branch

L1373:	staa MapValue	    ; store a into memory
L1374:	staa MapVolts	    ; store a into memory
L1375:	ldaa MapVolts	    ; load a with memory contents
	suba CPU_A2DResults1
	bcc  L1376	    ; branch if greater or equal
	nega		    ; negate a (set high bit)
L1376:	ldab MPDELT_DeltaMapThatChecksGood    ; load b with memory contents (data is 01)
	brclr *b45_IPL1, #b45_MapStuck, L1377    ; branch if bit(s) clear
	addb MPDELA_MatureMapLimpinWhenDeltaAbove_MPDELT_plus_MPDELA	    ;  (data is 01)
L1377:	cba
	bcs  R1380	    ; branch if lower
	bset *BitFlags_54, #b54_BigMapChange	; set bits
	brclr *b45_IPL1, #b45_MapStuck, R1380    ; branch if bit(s) clear
	ldab Counter_MainLoop	  ; load b with memory contents
	bitb #0x1f	    ;  -00011111-
	bne  R1380	    ; branch if not equal (not zero)
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	cmpD #0x0040            ; compare D -00000000 01000000-
	bcc  L1379	    ; branch if greater or equal
	brset *BitFlags_4f, #b4f_OffIdle, L1379    ; branch if bit(s) set
	ldd  EngineRpm_HB    ; load d (a&b) with memory contents
	subd TargetIdleSpeed_HB	; d = d - memory contents
	bcc  L1378	    ; branch if greater or equal
	coma		
	comb		
L1378:	cmpD MPRMPD_CheckMapAtZeroSpeedAndThisDeltaRpm	  ; compare D (data is 02)
	bcs  R1380	    ; branch if lower
L1379:	ldaa #0x08	    ; load a with value -00001000-
	jmp  ResetErrorCodeIfTimerExpired

R1380:	rts		    ; return from subroutine

VerifyOperationOfMapSensor_MM:
	ldaa Counter_MainLoop	  ; load a with memory contents
	bita #0x07	    ;  -00000111-
	bne  R1380	    ; branch if not equal (not zero)
	brset *b45_IPL1, #b45_MapStuck, L1384    ; branch if bit(s) set
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	cmpD #0x0040    ; compare D -00000000 01000000-
	bcc  L1384	    ; branch if greater or equal
	brset *BitFlags_4f, #b4f_OffIdle, L1384    ; branch if bit(s) set
	ldd  EngineRpm_HB    ; load d (a&b) with memory contents
	subd TargetIdleSpeed_HB	; d = d - memory contents
	bcc  L1381	    ; branch if greater or equal
	coma		
	comb		
L1381:	cmpD MPRMPD_CheckMapAtZeroSpeedAndThisDeltaRpm	  ; compare D (data is 02)
	bcc  L1384	    ; branch if greater or equal
	brset *BitFlags_54, #b54_FuelEngineNotRunning, L1384	; branch if bit(s) set
	ldaa BaroPressure    ; load a with memory contents
	tab		    ; b = a
	suba MapValue	
	bcs  L1383	    ; branch if lower
	ldx  #MPVACD_AllowMapToTestGoodThisNearBaro    ; load index with value
	cmpb BAROSW_CheckMapAtZeroSpeedAndThisBaroSwitch    ; compare b with memory contents (data is 41)
	bcc  L1382	    ; branch if greater or equal
	inx		    ; increment index (x=x+1)
L1382:	cmpa 0x00,x	    ; compare a with memory at index + value
	bcc  L1384	    ; branch if greater or equal
L1383:	ldd  #0x2794	    ; load d (a&b) with value -00100111 10010100-
	jsr  ThrowNonCriticalError    ; call subroutine
	bcc  L1384	    ; branch if greater or equal
	bset *b45_IPL1, #b45_MapStuck    ; set bits
L1384:	ldx  EngineRpm_HB
	cpx  #0x2ee0	    ;  -00101110 11100000-
	bcc  R1380	    ; branch if greater or equal
	ldab TpsVolts	    ; load b with memory contents
	subb MINTHR_LowestSessionTPS	; b = b-memory contents
	bcs  L1385	    ; branch if lower
	cmpb MPLTHR_ThrottleLevelAbove_MINTHR_ToMatureMapLimpin    ; compare b with memory contents (data is 42)
	bcc  R1380	    ; branch if greater or equal
L1385:	ldaa CPU_A2DResults1	; load a with memory contents
	cmpa MAPHIG_MapSensorUpperLimit    ; compare a with memory contents (data is ee)
	bcc  L1386	    ; branch if greater or equal
	cmpa MAPLOW_MapSensorLowerLimit    ; compare a with memory contents (data is 01)
	bcc  L1389	    ; branch if greater or equal
	ldd  #0x2494	    ; load d (a&b) with value -00100100 10010100-
	bra  L1387	    ; branch

L1386:	ldd  #0x2594	    ; load d (a&b) with value -00100101 10010100-
L1387:	brset *b45_IPL1, #b45_MapBadSignal, R1388	; branch if bit(s) set
	jsr  ThrowNonCriticalError    ; call subroutine
	bcc  R1388	    ; branch if greater or equal
	bset *b45_IPL1, #b45_MapBadSignal	; set bits
R1388:	rts		    ; return from subroutine

L1389:	brclr *b45_IPL1, #b45_MapBadSignal, R1388	; branch if bit(s) clear
	ldaa #0x06	    ; load a with value -00000110-
ResetErrorCodeIfTimerExpired:
	anda #0x0f	    ; AND a with value -00001111-
	ldab ERRORCODERESETTIMERIN_UN_ERRORCODEIN_LN_VAR    ; load b with memory contents
	beq  L1390	    ; branch if equal (zero)
	andb #0x0f	    ;  -00001111-
	cba		
	bne  R1391	    ; branch if not equal (not zero)
	ldaa ERRORCODERESETTIMERIN_UN_ERRORCODEIN_LN_VAR    ; load a with memory contents
L1390:	adda #0x10	    ;  -00010000-
	bcs  SELECT_ERROR_BIT_POSITION_ROUT    ; branch if lower
	staa ERRORCODERESETTIMERIN_UN_ERRORCODEIN_LN_VAR    ; store a into memory
R1391:	rts		    ; return from subroutine

SELECT_ERROR_BIT_POSITION_ROUT:
	ldab #0x01	    ; load b with value -00000001-
L1392:	deca		    ; decrement a
	beq  L1393	    ; branch if equal (zero)
	lslb		
	bra  L1392	    ; branch

L1393:	clr  ERRORCODERESETTIMERIN_UN_ERRORCODEIN_LN_VAR    ; zero byte at memory location
	comb		
	sei		    ; disable interrupts
	andb b45_IPL1
	stab b45_IPL1    ; store b into memory
	cli		    ; enable interrupts
	rts		    ; return from subroutine

SetupSystemRegisters:
	ldd  #0x9975	    ; load d (a&b) with value -10011001 01110101-
	staa CPU_SysConfigOptionReg
	stab CPU_HighPriorityInterruptMask    ; store b into memory
	ldd  #0x0002	 ; load d (a&b) with value -00000000 00000010-
	staa CPU_PulseAccumulatorControl
	stab CPU_TimerInterruptMask2	; Set timer prescaler to 8; timer resolution = 4uSec per tick
	clra		    ; a = 0
	staa CPU_OutputCompare1Mask
	staa BitFlags_2e    ; store a into memory
	ldaa CPU_BlockProtReg	 ; load a with memory contents
	anda #0xf8	    ; AND a with value -11111000-
	staa CPU_BlockProtReg
	ldd  #0xfe78	    ; load d (a&b) with value -11111110 01111000-
	staa CPU_TimerControlReg1 ; set dwell to 'clear' on comapre; other to 'set' on compare
	stab CPU_TimerForceCompare    ; store b into memory
	ldd  CPU_TimerCounterRegHigh
	addd #0x09c4	    ;  2.5ms
	xgDX		    ; exchange D and X
	ldaa #pia2b_bit2	  ; load a with value -00000100-
	staa PIA2_PortB_ControlRegister
L1394:	ldab PIA2_PortB_DataDirection	 ; load b with memory contents
	bitb #pia2b_OC1Toggle	    ;  -00001000-
	bne  L1396	    ; branch if not equal (not zero)
	bitb #pia2b_bit2|pia2b_IgnCoilDriverSense|pia2b_InjectorDriverSense	    ;  -00000111-
	beq  L1397	    ; branch if equal (zero)
	cpx  CPU_TimerCounterRegHigh
	bpl  L1394	    ; branch if plus (hi bit 0)
	bset *BitFlags_2e, #b2e_bit3	; set bits
L1395:	clc		    ; clear carry
	rts		    ; return from subroutine

L1396:	bitb #0x07	    ;  -00000111-
	bne  L1395	    ; branch if not equal (not zero)
	cpx  CPU_TimerCounterRegHigh
	bpl  L1394	    ; branch if plus (hi bit 0)
L1397:	sec		    ; set carry
	rts		    ; return from subroutine

CountRamValuesFrom02to2e:
	clra		    ; a = 0
	clrb		    ; b = 0
	ldx  #0x0002	    ; load index with value
L1398:	addb 0x00,x	    ; add memory at index + value to b
	bcc  L1399	    ; branch if greater or equal
	inca		    ; increment a
L1399:	inx		    ; increment index (x=x+1)
	cpx  #0x002e         ;	-00000000 00101110-
	bcs  L1398	    ; branch if lower
	rts		    ; return from subroutine

VerifyOperationOfThermostat_MM:
	brset *BitFlags_54, #b54_FuelEngineNotRunning, R1403	; branch if bit(s) set
	brset *b45_IPL1, #b45_BadCoolantTemp, R1403	  ; branch if bit(s) set
	ldaa Timer_ThermostatDiagnostics    ; load a with memory contents
	beq  R1403	    ; branch if equal (zero)
	ldab Counter_MainLoop	  ; load b with memory contents
	bne  R1403	    ; branch if not equal (not zero)
	ldab CoolantTemp    ; load b with memory contents
	cmpb TDAGTP_TstatDiagnosticsTemperatureGoalWithin_HOTIME    ; compare b with memory contents (data is c7)
	bcc  L1401	    ; branch if greater or equal
	ldab KeyOnOrEngineRunningTime	 ; load b with memory contents
	incb		
	bne  R1403	    ; branch if not equal (not zero)
	ldab VehicleSpeed_HB	; load b with memory contents
	cmpb #0x07	    ;  -00000111-
	bcs  R1403	    ; branch if lower
	inca		    ; increment a
	beq  L1400	    ; branch if equal (zero)
	cmpa HOTIME_TstatDiagnosticsTimeToAchieveTemperatureGoal    ; compare a with memory contents (data is ae)
	bcs  L1402	    ; branch if lower
L1400:	ldd  #0x2101	    ; load d (a&b) with value -00100001 00000001-
	jsr  ThrowNonCriticalError    ; call subroutine
	bcc  R1403	    ; branch if greater or equal
L1401:	clra		    ; a = 0
L1402:	staa Timer_ThermostatDiagnostics    ; store a into memory
R1403:	rts		    ; return from subroutine

VerifyOperationOfASDRelayAndO2Sensor_MM:
	ldaa CountdownTimerFromKeyOn	; load a with memory contents
	bne  R1407	    ; branch if not equal (not zero)
	ldab Counter_MainLoop	  ; load b with memory contents
	bitb #0x03	    ;  -00000011-
	bne  R1407	    ; branch if not equal (not zero)
	ldaa TimerOverflowsBetweenDistPulses	; load a with memory contents
	bne  L1404	    ; branch if not equal (not zero)
	brset *StartupSwitchMirror2, #sw2_B1Volt, L1404    ; branch if bit(s) set
	ldd  #0x2c14	    ; load d (a&b) with value -00101100 00010100-
	jsr  ThrowNonCriticalError    ; call subroutine
L1404:	ldaa Counter_MainLoop	  ; load a with memory contents
	bita #0x7f	    ;  -01111111-
	bne  R1407	    ; branch if not equal (not zero)
	ldaa CoolantTemp    ; load a with memory contents
	cmpa CTLRPM_LowBatteryVoltageAtThisCoolantTemp	  ; compare a with memory contents (data is cd)
	bcs  R1407	    ; branch if lower
	ldaa EngineRpm_HB    ; load a with memory contents
	cmpa BTLRPM2_LowBatteryVoltageAtThisRpm1500    ; compare a with memory contents (data is 2e)
	bcs  R1407	    ; branch if lower
	brset *BitFlags_4f, #b4f_O2Valid, L1406    ; branch if bit(s) set
	ldaa O2SensorValue    ; load a with memory contents
	cmpa O2MIDL_LowLimitForInMiddleDetermination	; compare a with memory contents (data is 12)
	bcs  L1406	    ; branch if lower
	cmpa O2MIDH_HighLimitForInMiddleDetermination	 ; compare a with memory contents (data is 1c)
	bcc  L1406	    ; branch if greater or equal
	brset *BitFlags_50, #b50_BadO2, L1406	 ; branch if bit(s) set
	ldaa Timer_O2MiddleDiagnostics	 ; load a with memory contents
	inca		    ; increment a
	beq  L1405	    ; branch if equal (zero)
	staa Timer_O2MiddleDiagnostics	 ; store a into memory
	cmpa #0x56	    ; compare a with value -01010110-
	bcs  R1407	    ; branch if lower
L1405:	ldd  #0x2001	    ; load d (a&b) with value -00100000 00000001-
	jsr  ThrowCriticalError    ; call subroutine
	bcc  R1407	    ; branch if greater or equal
	bset *BitFlags_50, #b50_BadO2	 ; set bits
L1406:	clra		    ; a = 0
	staa Timer_O2MiddleDiagnostics    ; store a into memory
R1407:	rts		    ; return from subroutine

DealWithConfigurationAndPulseAccumulator_MM:
	ldx  #CPU_PortA 	; load index with value
	ldaa CPU_OutputCompare1Mask    ; load a with memory contents
	bita #0xf8	    ;  -11111000-
	beq  L1408	    ; branch if equal (zero)
	clr  CPU_OutputCompare1Mask    ; zero byte at memory location
L1408:	ldd  CPU_TimerControlReg2
	bita #0x08	    ;  -00001000-
	bne  L1409	    ; branch if not equal (not zero)
	bset 33, X, #$%00001000    ; bit set
L1409:	bita #0x07	    ;  -00000111-
	beq  L1410	    ; branch if equal (zero)
	bclr 33, X, #$%00000111    ; bit clear
L1410:	brset 34, X, #$%11001110, L1411    ; branch if bit(s) set
	bset 34, X, #$%11001110    ; bit set
L1411:	bitb #0x31	    ;  -00110001-
	beq  L1412	    ; branch if equal (zero)
	bclr 34, X, #$%00110001    ; bit clear
L1412:	ldaa CPU_TimerInterruptMask2	; load a with memory contents
	bita #0xf1	    ;  -11110001-
	beq  L1413	    ; branch if equal (zero)
	bclr 36, X, #$%11110001    ; bit clear
L1413:	bita #0x02	    ;  -00000010-
	bne  L1414	    ; branch if not equal (not zero)
	bset 36, X, #$%00000010    ; bit set
L1414:	ldaa CPU_PulseAccumulatorControl    ; load a with memory contents
	beq  L1415	    ; branch if equal (zero)
	bclr 38, X, #$%11111111    ; bit clear
L1415:	ldaa #0x54	    ; load a with value -01010100-
	cmpa CPU_SerialPeripheralControl    ; compare a with memory contents
	beq  L1416	    ; branch if equal (zero)
	staa CPU_SerialPeripheralControl
L1416:  ldd  #0x000c
	cmpD CPU_SerialControl1    ; compare D
	beq  L1417	    ; branch if equal (zero)
	std  CPU_SerialControl1
L1417:	ldaa CPU_SysConfigOptionReg    ; load a with memory contents
	brset 57, X, #$%10001000, L1418    ; branch if bit(s) set
	bset 57, X, #$%10001000    ; bit set
L1418:	bita #0x40	    ;  -01000000-
	beq  L1419	    ; branch if equal (zero)
	bclr 57, X, #$%01000000    ; bit clear
L1419:	brset 60, X, #$%00000101, L1420    ; branch if bit(s) set
	sei		    ; disable interrupts
	bset 60, X, #$%00000101    ; bit set
	cli		    ; enable interrupts
L1420:	ldaa CPU_HighPriorityInterruptMask    ; load a with memory contents
	bita #0x0a	    ;  -00001010-
	beq  R1421	    ; branch if equal (zero)
	sei		    ; disable interrupts
	bclr 60, X, #$%00001010    ; bit clear
	cli		    ; enable interrupts
R1421:	rts		    ; return from subroutine

VerifyOperationOfIgnitionCoilDriver2_MM:
	ldaa TimerOverflowsBetweenDistPulses	; load a with memory contents
	cmpa #0x28	    ; compare a with value -00101000-
	bcs  L1423	    ; branch if lower
	ldaa CountdownTimerFromKeyOn	; load a with memory contents
	bne  R1424	    ; branch if not equal (not zero)
	ldaa SwitchPortAccessReg    ; load a with memory contents
	tab		    ; b = a
	eorb BitFlags_53
	andb #b53_bit5		;  -00100000-
	beq  L1422	    ; branch if equal (zero)
	anda #swp_DistSync	    ; AND a with value -00100000-
	ldab BitFlags_53    ; load b with memory contents
	andb #~b53_bit5 	 ;  -11011111-
	aba		    ; a=a+b
	staa BitFlags_53    ; store a into memory
	bclr *BitFlags_53, #b53_bit0	; clear bits
L1422:	brset *BitFlags_53, #b53_bit0, R1424	; branch if bit(s) set
	ldaa Counter_MainLoop	  ; load a with memory contents
	bita #0x0f	    ;  -00001111-
	bne  R1424	    ; branch if not equal (not zero)
	ldaa BatteryVolts    ; load a with memory contents
	cmpa #0x41	    ; compare a with value -01000001-
	bcs  R1424	    ; branch if lower
	cmpa COILHI_HiLimitBatteryVoltsForCoilVerify	; compare a with memory contents (data is ba)
	bcc  R1424	    ; branch if greater or equal
	ldaa MapValue	    ; load a with memory contents
	suba MapVolts	
	bls  R1424	    ; branch if lower or same
	cmpa COILLO_LoLimitBatteryVoltsForCoilVerify	; compare a with memory contents (data is 03)
	bcs  R1424	    ; branch if lower
	ldd  #0x2814	    ; load d (a&b) with value -00101000 00010100-
	jmp  ThrowNonCriticalError

L1423:	bset *BitFlags_53, #b53_bit0	; set bits
R1424:	rts		    ; return from subroutine

CallAndReturn1:
	rts		    ; return from subroutine

BYTE_MODE_SERIAL_CODE_DOWNLOAD_ROUTINE:
	rts		    ; return from subroutine

; EmmissionMaintenanceRemider1_MM:
;         ldaa OPTN2_CalCustomOptionConfigFlags2
;         bita #opt_Bit2
;         beq  EMR_Normal1
;         rts
; ;
; EMR_Normal1:
; 	bset *BitFlags_2d, #b2d_EMR	; set bits
; 	ldaa CPU_EEPROMControlReg    ; load a with memory contents
; 	bne  L1425	    ; branch if not equal (not zero)
; 	ldd  LB610	    ;  (data is ffff)
; 	subd #0x5aa5	    ;  -01011010 10100101-
; L1425:	brclr *BitFlags_54, #b54_FuelEngineNotRunning, L1426	; branch if bit(s) clear
; 	ldaa KeyOnOrEngineRunningTime	 ; load a with memory contents
; L1426:	bne  L1427	    ; branch if not equal (not zero)
; 	bclr *BitFlags_2d, #b2d_EMR	; clear bits
; L1427:	sei		    ; disable interrupts
; 	brset *BitFlags_52, #b52_DRBToggle1, L1430    ; branch if bit(s) set
; 	brset *b46_IPL2, #b46_bit0, L1431	; branch if bit(s) set
; 	brclr *BitFlags_52, #b52_EMR, L1430    ; branch if bit(s) clear
; 	bset *BitFlags_52, #b52_DRBToggle1    ; set bits
; 	cli		    ; enable interrupts
; 	ldaa #0x10	    ; load a with value -00010000-
; 	ldab #0x5a	    ; load b with value -01011010-
; 	brclr *BitFlags_52, #b52_DRBToggle2, L1428    ; branch if bit(s) clear
; 	cmpa DRBOffsetStored_HB    ; compare a with memory contents
; 	bne  L1438	    ; branch if not equal (not zero)
; 	inca		    ; increment a
; 	comb		
; 	bclr *BitFlags_52, #b52_EMR | b52_DRBToggle2    ; clear bits
; 	bra  L1429	    ; branch
; 
; L1428:	bset *BitFlags_52, #b52_DRBToggle2    ; set bits
; L1429:	staa DRBOffsetStored_HB    ; store a into memory
; 	stab DRBOffsetStored_LB    ; store b into memory
; L1430:	cli		    ; enable interrupts
; 	rts		    ; return from subroutine
; 
; L1431:	bset *BitFlags_52, #b52_DRBToggle1    ; set bits
; 	cli		    ; enable interrupts
; 	brset *BitFlags_52, #b52_DRBToggle2, L1441    ; branch if bit(s) set
; 	ldx  #ErrorBitRegisterStored3	 ; load index with value
; 	ldab #0x30	    ; load b with value -00110000-
; L1432:	ldaa 0x00,x	    ; load a with memory at index + value
; 	beq  L1433	    ; branch if equal (zero)
; 	cba		
; 	beq  L1437	    ; branch if equal (zero)
; 	dex		    ; decrement index (x=x-1)
; 	cpx  #ErrorBitRegister0    ;  -00000000 00011110-
; 	bcc  L1432	    ; branch if greater or equal
; L1433:	clra		    ; a = 0
; 	clrb		    ; b = 0
; 	stD *Temp0	    ; store D to RAM
; 	ldx  #LB600	    ; load index with value
; L1434:	ldd  0x02,x
; 	cpx  #0xb60e	    ;  -10110110 00001110-
; 	bne  L1435	    ; branch if not equal (not zero)
; 	ldd  LB600	    ;  (data is ffff)
; L1435:	subd 0x00,x
; 	subd #0x0001	     ;	-00000000 00000001-
; 	bne  L1436	    ; branch if not equal (not zero)
; 	incb		
; 	addd 0x00,x	
; 	cmpD Temp0	    ; compare D
; 	bcs  L1436	    ; branch if lower
; 	stD *Temp0	    ; store D to RAM
; 	xgDX		    ; exchange D and X
; 	stab DRBOffsetStored_HB    ; store b into memory
; 	xgDX		    ; exchange D and X
; L1436:	inx		    ; increment index (x=x+1)
; 	inx		    ; increment index (x=x+1)
; 	cpx  #LB610	    ;  -10110110 00010000-
; 	bne  L1434	    ; branch if not equal (not zero)
; 	ldx  Temp0	
; 	bne  L1439	    ; branch if not equal (not zero)
; 	ldd  #0x3003	    ; load d (a&b) with value -00110000 00000011-
; 	jsr  ThrowNonCriticalError    ; call subroutine
; 	bcc  L1438	    ; branch if greater or equal
; L1437:	bclr *b46_IPL2, #b46_bit0	; clear bits
; L1438:	bclr *BitFlags_52, #b52_DRBToggle1    ; clear bits
; 	rts		    ; return from subroutine
; 
; L1439:	ldab DRBOffsetStored_HB    ; load b with memory contents
; 	addb #0x04	    ;  -00000100-
; 	cmpb #0x10	    ;  -00010000-
; 	blt  L1440	    ; branch if less
; 	subb #0x10	    ;  -00010000-
; L1440:	stab DRBOffsetStored_HB    ; store b into memory
; 	bsr  L1444	    ; call subroutine
; 	staa DRBOffsetStored_LB    ; store a into memory
; 	bset *BitFlags_52, #b52_DRBToggle2    ; set bits
; 	rts		    ; return from subroutine
; 
; L1441:	ldab DRBOffsetStored_HB    ; load b with memory contents
; 	cmpb #0x0e	    ;  -00001110-
; 	bhi  L1438	    ; branch if higher
; 	cmpb #0x00	    ;  -00000000-
; 	bcs  L1438	    ; branch if lower
; 	bsr  L1444	    ; call subroutine
; 	stab DRBOffsetStored_LB    ; store b into memory
; 	inc  DRBOffsetStored_HB
; 	bclr *b46_IPL2, #b46_bit0	; clear bits
; 	bclr *BitFlags_52, #b52_DRBToggle2    ; clear bits
; 	xgDX		    ; exchange D and X
; 	cpx  #0x1c9c	    ;  -00011100 10011100-
; 	beq  L1442	    ; branch if equal (zero)
; 	cpx  #0x2757	    ;  -00100111 01010111-
; 	beq  L1442	    ; branch if equal (zero)
; 	cpx  #0x3938	    ;  -00111001 00111000-
; 	bne  R1443	    ; branch if not equal (not zero)
; L1442:	bset *BitFlags_52, #b52_EMR    ; set bits
; R1443:	rts		    ; return from subroutine
; 
; L1444:	ldx  #LB600	    ; load index with value
; 	subb #0x02	    ;  -00000010-
; 	cmpb #0x00	    ;  -00000000-
; 	bge  L1445	    ; branch if greater or equal
; 	ldab #0x0e	    ; load b with value -00001110-
; L1445:	abx		    ; add b to index
; 	ldx  0x00,x	
; 	inx		    ; increment index (x=x+1)
; 	bne  L1446	    ; branch if not equal (not zero)
; 	dex		    ; decrement index (x=x-1)
; L1446:	xgDX		    ; exchange D and X
; 	rts		    ; return from subroutine
; 
; EmmissionMaintenanceRemider2_MM:
;         ldaa OPTN2_CalCustomOptionConfigFlags2
;         bita #opt_Bit2
;         beq  EMR_Normal2
;         rts
; ;
; EMR_Normal2:
; 	brset *Counter_MainLoop, #$%00000001, R1454	; branch if bit(s) set
; 	brclr *BitFlags_52, #b52_DRBToggle1, L1452    ; branch if bit(s) clear
; 	ldaa CountdownTimerFromKeyOn	; load a with memory contents
; 	beq  L1447	    ; branch if equal (zero)
; 	ldab #0x03	    ; load b with value -00000011-
; 	cba		
; 	bcc  L1447	    ; branch if greater or equal
; 	stab CountdownTimerFromKeyOn	; store b into memory
; L1447:	ldaa CPU_EEPROMControlReg    ; load a with memory contents
; 	clrb		    ; b = 0
; 	stab CPU_EEPROMControlReg    ; store b into memory
; 	ldx  #LB600	    ; load index with value
; 	ldab DRBOffsetStored_HB    ; load b with memory contents
; 	abx		    ; add b to index
; 	tab		    ; b = a
; 	ldaa 0x00,x	    ; load a with memory at index + value
; 	cmpa DRBOffsetStored_LB    ; compare a with memory contents
; 	beq  L1451	    ; branch if equal (zero)
; 	cmpb #0x03	    ;  -00000011-
; 	beq  L1448	    ; branch if equal (zero)
; 	bcs  L1449	    ; branch if lower
; 	ldab DRBOffsetStored_LB    ; load b with memory contents
; 	inca		    ; increment a
; 	beq  L1450	    ; branch if equal (zero)
; L1448:	brset *b46_IPL2, #b46_bit2, L1451	; branch if bit(s) set
; 	ldd  #0x318a	    ; load d (a&b) with value -00110001 10001010-
; 	jsr  ThrowNonCriticalError    ; call subroutine
; 	bcc  L1449	    ; branch if greater or equal
; 	bset *b46_IPL2, #b46_bit2	; set bits
; 	bra  L1451	    ; branch
; 
; L1449:	ldx  #LB600	    ; load index with value
; 	ldab DRBOffsetStored_HB    ; load b with memory contents
; 	abx		    ; add b to index
; 	ldab DRBOffsetStored_LB    ; load b with memory contents
; 	tba		    ; a = b
; 	anda 0x00,x	
; 	sba		    ; subtract (a=a-b)
; 	beq  L1450	    ; branch if equal (zero)
; 	ldaa #0x16	    ; load a with value -00010110-
; L1450:	oraa #0x02	    ;  -00000010-
; 	staa CPU_EEPROMControlReg
; 	stab 0x00,x	
; 	inca		    ; increment a
; 	bra  L1453	    ; branch
; 
; L1451:	bclr *BitFlags_52, #b52_DRBToggle1    ; clear bits
; 	brset *BitFlags_52, #b52_DRBToggle2, L1452    ; branch if bit(s) set
; 	ldaa CountdownTimerFromKeyOn	; load a with memory contents
; 	suba #0x03	    ;  -00000011-
; 	bne  L1452	    ; branch if not equal (not zero)
; 	inca		    ; increment a
; 	staa CountdownTimerFromKeyOn	; store a into memory
; L1452:	clra		    ; a = 0
; L1453:	staa CPU_EEPROMControlReg
; R1454:	rts		    ; return from subroutine

ExhGasRecirc_MM:
	ldaa CONFIG_ConfigurationFlags	  ; load a with memory contents (data is 02)
	bita #cfg_EGR	       ;  -01000000-
	bne  EGR_CheckForAutoTrans    ; branch if not equal (not zero)
	jmp  L1469	

EGR_CheckForAutoTrans:
	bita #cfg_ATX		;  -00100000-
	bne  L1456	    ; branch if not equal (not zero)
	brclr *BitFlags_4f, #b4f_OffIdle, L1457    ; branch if bit(s) clear
	ldaa EGR13_ExhGasRecircConstFromRPM    ; load a with memory contents (data is 00)
	ldab EGR11_ExhGasRecircConstFromMAP    ; load b with memory contents (data is 00)
	brset *BitFlags_2d, #b2d_EGR, L1455	; branch if bit(s) set
	adda EGR10_ExhGasRecircConstFromRPM    ;  (data is 00)
	addb EGR12_ExhGasRecircConstFromMAP    ;  (data is 00)
L1455:	cmpa EngineRpm_HB    ; compare a with memory contents
	bls  L1456	    ; branch if lower or same
	cmpb MapValue	
	bhi  L1457	    ; branch if higher
L1456:	ldaa KeyOnOrEngineRunningTime	 ; load a with memory contents
	cmpa EGR9_ExhGasRecircConstFromTimeEngRunning	  ; compare a with memory contents (data is 80)
	bcs  L1459	    ; branch if lower
	brset *BitFlags_4f, #b4f_OffIdle, L1458    ; branch if bit(s) set
L1457:	bset *EGRVar2, #bit_bit4	  ; set bits
	jmp  EGR_SetEGRtoOff

L1458:	brset *EGRVar2, #bit_bit6, EGR_ResetEGRVars    ; branch if bit(s) set
	brset *EGRVar2, #bit_bit4, EGR_ResetEGRVars    ; branch if bit(s) set
	brclr *BitFlags_4f, #b4f_O2Valid, EGR_ResetEGRVars    ; branch if bit(s) clear
	brset *BitFlags_50, #b50_StayOpenLoop, EGR_ResetEGRVars    ; branch if bit(s) set
	ldd  IPLMSK_PowerLossLightMask	  ;  (data is fed8)
	bita b45_IPL1
	bne  EGR_ResetEGRVars	 ; branch if not equal (not zero)
	bitb b46_IPL2
	bne  EGR_ResetEGRVars	 ; branch if not equal (not zero)
	brclr *PIA1_A_Buffer, #pia1abuf_PurgeSolenoid, EGR_ResetEGRVars    ; branch if bit(s) clear
	ldaa BaroPressure    ; load a with memory contents
	suba MapValue	
L1459:	bcs  EGR_ResetEGRVars	 ; branch if lower
	cmpa EGR33_ExhGasRecircConstFromMAPBelowBaro	 ; compare a with memory contents (data is 08)
	bcs  EGR_ResetEGRVars	 ; branch if lower
	ldx  EGRVar3
	brset *EGRVar2, #bit_bit7, L1467	; branch if bit(s) set
	cpx  EGR1_ExhGasRecircConst	;  (data is 01c7)
	bhi  L1466	    ; branch if higher
	ldaa MapValue	    ; load a with memory contents
	ldx  #EGR18_ExhGasRecircConstLoLimit	; load index with value
	bsr  EGR_CheckHiLoLimits    ; call subroutine
	ldaa TpsVolts	    ; load a with memory contents
	suba MINTHR_LowestSessionTPS
	bls  EGR_ResetEGRVars	 ; branch if lower or same
	ldx  #EGR14_ExhGasRecircConstFromTPSVoltsLoLimit    ; load index with value
	bsr  EGR_CheckHiLoLimits    ; call subroutine
	ldaa EngineRpm_HB    ; load a with memory contents
	ldx  #EGR15_ExhGasRecircConstFromRPMLoLimit    ; load index with value
	bsr  EGR_CheckHiLoLimits    ; call subroutine
	ldaa Counter_PrimaryAndSecondaryRamp    ; load a with memory contents
	cmpa EGR3_ExhGasRecircConst	; compare a with memory contents (data is 80)
	bge  EGR_ResetEGRVars	 ; branch if greater or equal
	ldx  EGRVar3
	inx		    ; increment index (x=x+1)
	stx  EGRVar3    ; store index into memory
	ldab EGR8_ExhGasRecircConst	; load b with memory contents (data is 81)
	suba EGRVar5
	bvc  L1462	    ; branch if overflow
	bmi  L1463	    ; branch if minus(hi bit 1)
L1460:	nega		    ; negate a (set high bit)
	mul		    ; multiply (d=a*b)
	adca #0x00	    ;  -00000000-
	nega		    ; negate a (set high bit)
L1461:	adda EGRVar5
	staa EGRVar5    ; store a into memory
	bra  L1465	    ; branch

L1462:	bmi  L1460	    ; branch if minus(hi bit 1)
L1463:	mul		    ; multiply (d=a*b)
	adca #0x00	    ;  -00000000-
	bra  L1461	    ; branch

EGR_CheckHiLoLimits:
	cmpa 0x00,x	    ; compare a with memory at index + value
	bcs  L1464	    ; branch if lower
	cmpa 0x01,x	    ; compare a with memory at index + value
	bhi  L1464	    ; branch if higher
	rts		    ; return from subroutine

L1464:	pulx		    ; pull index from stack
EGR_ResetEGRVars:
	clra		    ; a = 0
	clrb		    ; b = 0
	stD *EGRVar3    ; store D to RAM
	bclr *EGRVar2, #bit_bit7 | bit_bit4	  ; clear bits
	ldaa Counter_PrimaryAndSecondaryRamp    ; load a with memory contents
	staa EGRVar5    ; store a into memory
L1465:	jmp  EGR_SetEGRtoOn

L1466:	ldx  #0x0000	     ; load index with value
	bset *EGRVar2, #bit_bit7	; set bits
	ldaa EGRVar5    ; load a with memory contents
	staa EGRVar6    ; store a into memory
	bra  L1468	    ; branch

L1467:	cpx  EGR6_ExhGasRecircConst	;  (data is 016c)
	bcc  L1470	    ; branch if greater or equal
L1468:	inx		    ; increment index (x=x+1)
	stx  EGRVar3    ; store index into memory
	ldaa MapValue	    ; load a with memory contents
	ldx  #EGR16_ExhGasRecircConstLoLimit	; load index with value
	bsr  EGR_CheckHiLoLimits    ; call subroutine
	ldaa TpsVolts	    ; load a with memory contents
	suba MINTHR_LowestSessionTPS
	bls  EGR_ResetEGRVars	 ; branch if lower or same
	ldx  #EGR19_ExhGasRecircConstLoLimit	; load index with value
	bsr  EGR_CheckHiLoLimits    ; call subroutine
	ldaa EngineRpm_HB    ; load a with memory contents
	ldx  #EGR17_ExhGasRecircConstLoLimit	; load index with value
	bsr  EGR_CheckHiLoLimits    ; call subroutine
	ldaa Counter_PrimaryAndSecondaryRamp    ; load a with memory contents
	cmpa EGRVar6    ; compare a with memory contents
	ble  L1474	    ; branch if less or equal
	staa EGRVar6    ; store a into memory
	suba EGRVar5
	staa EGRVar7    ; store a into memory
	cmpa EGR7_ExhGasRecircConst	; compare a with memory contents (data is 00)
	bcs  L1474	    ; branch if lower
L1469:	clr  EGRVar1    ; zero byte at memory location
	bset *EGRVar2, #bit_bit6	; set bits
	bclr *EGRVar2, #bit_bit7	; clear bits
	bclr *b46_IPL2, #b46_bit7	; clear bits
	bra  EGR_SetEGRtoOn	        ; branch

L1470:	clra		    ; a = 0
	clrb		    ; b = 0
	stD *EGRVar3    ; store D to RAM
	ldaa EGRVar1    ; load a with memory contents
	inca		    ; increment a
	staa EGRVar1    ; store a into memory
	cmpa EGR4_ExhGasRecircConst	; compare a with memory contents (data is eb)
	bcs  L1471	    ; branch if lower
	ldd  #0x2e01	    ; load d (a&b) with value -00101110 00000001-
	jsr  ThrowNonCriticalError    ; call subroutine
	bset *b46_IPL2, #b46_bit7	; set bits
L1471:	ldab EGRVar2    ; load b with memory contents
	andb #~bit_bit7	    ;  -01111111-
	tba		    ; a = b
	inca		    ; increment a
	anda #bit_bothalf	    ; AND a with value -00001111-
	beq  L1472	    ; branch if equal (zero)
	incb		
	cmpa EGR5_ExhGasRecircConst	; compare a with memory contents (data is 00)
	bcs  L1473	    ; branch if lower
L1472:	orab #bit_bit6	    ;  -01000000-
L1473:	stab EGRVar2    ; store b into memory
L1474:	brclr *EGRVar2, #bit_bit7, EGR_SetEGRtoOn    ; branch if bit(s) clear

EGR_SetEGRtoOff:
	bclr *BitFlags_2d, #b2d_EGR	; clear bits
	rts		    ; return from subroutine

EGR_SetEGRtoOn:
	bset *BitFlags_2d, #b2d_EGR	; set bits
	rts		    ; return from subroutine

CalculateInjectorPulsewidthForStarting_MM:
	brset *BitFlags_54, #b54_FuelEngineNotRunning, L1475	; branch if bit(s) set
	rts		    ; return from subroutine

L1475:	clra		    ; a = 0
	clrb		    ; b = 0
	stD *Pulsewidth_PartThrottleEnrichment_HB    ; store D to RAM
	ldaa TpsVolts	    ; load a with memory contents
	cmpa #0xd0	    ; compare a with value -11010000-
	bcc  ThrottleFlooredWhileStarting_UnloadFuel	; branch if greater or equal
	suba MINTHR_LowestSessionTPS
	bls  L1476	    ; branch if lower or same
	cmpa UNLOAD_DeltaThrottleFrom_MINTHR_ToUnloadCrankingFuel    ; compare a with memory contents (data is 85)
	bcc  ThrottleFlooredWhileStarting_UnloadFuel	; branch if greater or equal
L1476:	jsr  AllowForHeatSoakAfterStall    ; call subroutine
	brset *BitFlags_4f, #b4f_OffIdle, L1477    ; branch if bit(s) set
	cmpa STRLMT_ColdestTempAllowedAtClosedThrottle	  ; compare a with memory contents (data is 69)
	bcc  L1477	    ; branch if greater or equal
	ldaa STRLMT_ColdestTempAllowedAtClosedThrottle	  ; load a with memory contents (data is 69)
L1477:	ldx  #STRTFL_FuelStartFromCoolantTemp	 ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	mul		    ; multiply (d=a*b)
	stD *Temp0	    ; store D to RAM
	ldaa Counter_EPP_MaxFF	  ; load a with memory contents
	ldx  #EPPMUL_FuelStartFuelPerEPP    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	ldY Temp0	    ; load Y index
	jsr  ScaleYbyA	    ; call subroutine
	stY Temp0	    ; store Y index
	ldaa BaroPressure    ; load a with memory contents
	ldx  #STFBAR_FuelStartReductionFromBaro    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Temp4	    ; store a into memory
	ldaa CoolantTemp    ; load a with memory contents
	ldx  #STFTMP_FuelStartFuelFromCoolant	 ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	ldaa Temp4	    ; load a with memory contents
	mul		    ; multiply (d=a*b)
	adca #0x00	    ;  -00000000-
	beq  L1478	    ; branch if equal (zero)
	nega		    ; negate a (set high bit)
	ldY Temp0	    ; load Y index
	jsr  ScaleYbyA	    ; call subroutine
	xgDY		    ; exchange D and Y
	bra  L1479	    ; branch

L1478:	ldd  Temp0	    ; load d (a&b) with memory contents
	bra  L1479	    ; branch

ThrottleFlooredWhileStarting_UnloadFuel:
	clra		    ; a = 0
	clrb		    ; b = 0
L1479:	jsr  CallAndReturn1    ; call subroutine
	stD *InjectorPulsewidth_HB    ; store D to RAM
	cli		    ; enable interrupts
	ldx  #SFDCAY_FuelStartDecayIntoRun    ; load index with value
	ldaa CoolantTemp    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Factor_StartFuelDecayIntoRunFuel	 ; store a into memory
	rts		    ; return from subroutine

ControlEngineCutout_MM:
	brset *Turbonator_Flags, #Turbonator_Staging, R1000 ; added to keep the normal rev limiter code from turning off the staging limiter...

        brclr *TimerOverflowsBetweenDistPulses, #$%11111111, EngineRunning    ; branch if bit(s) clear
	bclr *Turbonator_Flags, #Turbonator_FuelOff | Turbonator_OverRev	 ; clear bits
R1000:	rts		    ; return from subroutine

EngineRunning:
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
        staa Temp1          ; store 255mph speed to temp1 for future use
	asld		    ; shift left (d=d*2)
	bcc  Cutout_SpeedIsBelow128Mph	  ; branch if greater or equal
	ldaa #0xff	    ; load a with value -11111111-
Cutout_SpeedIsBelow128Mph:
	staa Temp0	    ; store a into memory
	brclr *Turbonator_Flags, #Turbonator_FuelOff, Cutout_UseDecelFuelCut    ; branch if bit(s) clear
	jmp  Cutout_UseHysteresisToDetermineWhenToTurnFuelBackOn

Cutout_UseDecelFuelCut:
        brclr *Turbonator_Flags, #Turbonator_DecelFuelCut, Cutout_CheckForOBConditions    ; branch if bit(s) clear
        ldd  EngineRpm_HB    ; load d (a&b) with memory contents
        subd TargetIdleSpeed_HB    ; d = d - memory contents
        bcc  LBA1B          ; branch if greater or equal
        clra                ; a = 0
LBA1B:  cmpa DFRPMH_DecelFuelShutoffDeltaRPMOff    ; compare a with memory contents (data is 1e)
        bls  Cutout_CheckForOBConditions          ; branch if lower or same
        bset *Turbonator_Flags, #Turbonator_FuelOff    ; set bits
        rts                 ; return from subroutine

Cutout_CheckForOBConditions:
	ldaa MapValue	                       ; load a with memory contents
	suba BaroPressure
	bcs  Cutout_ResetOverboostTimer                ; branch if lower
	brclr *b46_IPL2, #b46_WGSolFault, Cutout_CheckNormalOB	; branch if bit(s) clear
	cmpa LMPSHF_OverboostFuelShutoffDisablePointFromMap_Limp     ; compare a with memory contents (data is ff)
	bls  Cutout_CheckRevLimiters	       ; branch if lower or same

Cutout_ShutOffEngineForThisRotation:
	bclr *Turbonator_Flags, #Turbonator_OverRev        ; clear bits
	bset *Turbonator_Flags, #Turbonator_FuelOff        ; set bits
	rts		                       ; return from subroutine

Cutout_ResetOverboostTimer:
	ldaa TRNTM_OverboostFuelShutoffDelay   ; load a with memory contents (data is ff)
	staa Timer_OverboostCountdown	       ; store a into memory
	bra  Cutout_CheckRevLimiters	       ; branch

Cutout_CheckNormalOB:	
        suba MPSHFT_OverboostFuelShutoffEnablePointFromMap_Timer    ;  (data is ff)
	bcs  Cutout_ResetOverboostTimer              ; branch if lower
	cmpa MPSHFA_OverboostFuelShutoffEnablePointFromMap_Absolute    ; compare a with memory contents (data is ff)
	bhi  Cutout_SetOBCodeAndShutdown       ; branch if higher
	ldaa Timer_OverboostCountdown	       ; load a with memory contents
	beq  Cutout_SetOBCodeAndShutdown       ; branch if equal (zero)
	deca		                       ; decrement a
	staa Timer_OverboostCountdown	       ; store a into memory
	bra  Cutout_CheckRevLimiters	       ; branch

Cutout_SetOBCodeAndShutdown:
	ldd  #0x0708	    ; load d (a&b) with value -00000111 00001000-
	jsr  ThrowNonCriticalError    ; call subroutine
	bra  Cutout_ShutOffEngineForThisRotation    ; branch

Cutout_CheckRevLimiters:
	ldx  #REVLMT2_MapLimpinAndThrAbove25PercentUpper2000	; load index with value
	brclr *b45_IPL1, #b45_MapStuck | b45_MapBadSignal, MAPSENSOR_OKAY_OR_LIGHTTHROTTLE	 ; branch if bit(s) clear
	ldab THRTHR_25PctThrValueFromShutoff	; load b with memory contents (data is 21)
	addb MINTHR_LowestSessionTPS	; b=b+memory contents
	cmpb TpsVolts	
	bcs  Cutout_CheckRevLimitingValues    ; branch if lower

MAPSENSOR_OKAY_OR_LIGHTTHROTTLE:
	ldx  #REVLMT4_MapAbove75PctAndThrLimpin2000    ; load index with value
	brclr *b45_IPL1, #b45_TpsBadSignal, THROTTLESENSOR_OKAY    ; branch if bit(s) clear
	ldaa Temp0	    ; load a with memory contents
	cmpa RVLSPD_CarSpeedForRevLimitWithTBOff    ; compare a with memory contents (data is 14)
	bcc  L1484	    ; branch if greater or equal
	bra  L1483	    ; branch

THROTTLESENSOR_OKAY:
	ldab BitFlags_4f    ; load b with memory contents
	bmi  L1484	    ; branch if minus(hi bit 1)
L1483:	ldab BaroPressure    ; load b with memory contents
	lsrb		    ; logical shift right b
	tba		    ; a = b
	lsrb		    ; logical shift right b
	aba		    ; a=a+b
	cmpa MapValue	    ; compare a with memory contents
	bcs  Cutout_CheckRevLimitingValues    ; branch if lower
L1484:	ldx  #REVLMT6_RPMLimiterNormalOffRPM	 ; load index with value

Cutout_CheckRevLimitingValues:
	ldaa EngineRpm_HB    ; load a with memory contents
	cmpa 0x00,x	    ; compare a with memory at index + value
	bcc  Cutout_ShutOffEngineForThisRotation    ; branch if greater or equal
	cmpa SPDRPM_EngineSpeedHighLimitToEnableOverspeed    ; compare a with memory contents (data is 7d)
	bcs  L1485	    ; branch if lower
	ldab Temp1	    ; load b with memory contents
	cmpb SPDLMH_SpeedLimitFuelShutoff254mph    ; compare b with memory contents (data is 76)
	bcc  Cutout_ShutOffEngineForThisRotation    ; branch if greater or equal
L1485:	brset *BitFlags_50, #b50_FallToIdle, Cutout_CheckMPHLimitingValues    ; branch if bit(s) set
	bclr *Turbonator_Flags, #Turbonator_OverRev    ; clear bits
	rts		    ; return from subroutine

Cutout_CheckMPHLimitingValues:
	cmpa DFRPM2_2560RPM_DecelFuelShutoffUpperRpmLimit    ; compare a with memory contents (data is db)
	bcs  R1487	    ; branch if lower
	ldaa Temp0	    ; load a with memory contents
	cmpa DFSMPH_20MPHDecelFuelShutoffSpeedLimit    ; compare a with memory contents (data is fe)
	bcs  R1487	    ; branch if lower
	ldaa CoolantTemp    ; load a with memory contents
	cmpa DFSTMP_60DegCDecelFuelShutoffTempLimit    ; compare a with memory contents (data is c0)
	bcs  R1487	    ; branch if lower
	ldaa KeyOnOrEngineRunningTime	 ; load a with memory contents
	cmpa DFSTMR_3minuteDecelFuelShutoffTimeLimit	; compare a with memory contents (data is 40)
	bcs  R1487	    ; branch if lower
	brset *Turbonator_Flags, #Turbonator_OverRev, R1487    ; branch if bit(s) set
	bset *Turbonator_Flags, #Turbonator_OverRev | Turbonator_FuelOff	 ; set bits
L1486:	clra		    ; a = 0
	staa Counter_PrimaryAndSecondaryRamp    ; store a into memory
R1487:	rts		    ; return from subroutine

Cutout_UseHysteresisToDetermineWhenToTurnFuelBackOn:
        brclr *Turbonator_Flags, #Turbonator_DecelFuelCut, LBB1C    ; branch if bit(s) clear
        ldd  EngineRpm_HB    ; load d (a&b) with memory contents
        subd TargetIdleSpeed_HB    ; d = d - memory contents
        bcc  LBB16          ; branch if greater or equal
        clra                ; a = 0
LBB16:  cmpa DFRPML_DecelFuelShutoffDeltaRPMOn    ; compare a with memory contents (data is 11)
        bls  Cutout_TurnFuelBackOn    ; branch if lower or same
        rts                 ; return from subroutine

LBB1C:	brclr *Turbonator_Flags, #Turbonator_OverRev, L1488    ; branch if bit(s) clear
	brclr *BitFlags_50, #b50_FallToIdle, Cutout_TurnFuelBackOn    ; branch if bit(s) clear
	ldaa EngineRpm_HB    ; load a with memory contents
	cmpa DFRPM1_2050RPM_DecelFuelShutoffTurnonLimit    ; compare a with memory contents (data is 40)
	bcc  L1486	    ; branch if greater or equal
Cutout_TurnFuelBackOn:
	bclr *Turbonator_Flags, #Turbonator_FuelOff    ; clear bits
	rts		    ; return from subroutine

L1488:	ldaa MapValue	    ; load a with memory contents
	suba BaroPressure
	bcs  Cutout_ResetOverboostTimerAgain	 ; branch if lower
	brclr *b46_IPL2, #b46_WGSolFault, L1489	; branch if bit(s) clear
	cmpa LMPSHF_OverboostFuelShutoffDisablePointFromMap_Limp    ; compare a with memory contents (data is ff)
	bls  Cutout_DetermineLimpModeCutoutRPM	  ; branch if lower or same
	rts		    ; return from subroutine

Cutout_ResetOverboostTimerAgain:
	ldaa TRNTM_OverboostFuelShutoffDelay    ; load a with memory contents (data is ff)
	staa Timer_OverboostCountdown	 ; store a into memory
	bra  Cutout_DetermineLimpModeCutoutRPM	  ; branch

L1489:	suba MPSHFT_OverboostFuelShutoffEnablePointFromMap_Timer    ;  (data is ff)
	bcs  Cutout_ResetOverboostTimerAgain	 ; branch if lower
	cmpa MPSHFA_OverboostFuelShutoffEnablePointFromMap_Absolute    ; compare a with memory contents (data is ff)
	bhi  L1490	    ; branch if higher
	ldaa Timer_OverboostCountdown	 ; load a with memory contents
	beq  L1490	    ; branch if equal (zero)
	deca		    ; decrement a
	staa Timer_OverboostCountdown	 ; store a into memory
	bra  Cutout_DetermineLimpModeCutoutRPM	  ; branch

L1490:	ldd  #0x0708	    ; load d (a&b) with value -00000111 00001000-
	jmp  ThrowNonCriticalError

Cutout_DetermineLimpModeCutoutRPM:
	ldx  #REVLMT_MapLimpinAndThrAbove25PercentLower1850    ; load index with value
	brclr *b45_IPL1, #b45_MapStuck | b45_MapBadSignal, MAPSENSOR_OKAY_OR_LIGHTTHROTTLE2	  ; branch if bit(s) clear
	ldab THRTHR_25PctThrValueFromShutoff	; load b with memory contents (data is 21)
	addb MINTHR_LowestSessionTPS	; b=b+memory contents
	cmpb TpsVolts	
	bcs  CHECK_IFOVER_1850_2000_6167RPM    ; branch if lower
MAPSENSOR_OKAY_OR_LIGHTTHROTTLE2:
	ldx  #REVLMT3_MapAbove75PctAndIdleSwitchClosed2000    ; load index with value
	brclr *b45_IPL1, #b45_TpsBadSignal, THROTTLESENSOR_OKAY2    ; branch if bit(s) clear
	ldaa Temp0	    ; load a with memory contents
	cmpa RVLSPD_CarSpeedForRevLimitWithTBOff    ; compare a with memory contents (data is 14)
	bcc  L1492	    ; branch if greater or equal
	bra  L1491	    ; branch

THROTTLESENSOR_OKAY2:
	ldab BitFlags_4f    ; load b with memory contents
	bmi  L1492	    ; branch if minus(hi bit 1) -- Off-idle
L1491:	ldab BaroPressure    ; load b with memory contents
	lsrb		    ; logical shift right b
	tba		    ; a = b
	lsrb		    ; logical shift right b
	aba		    ; a=a+b
	cmpa MapValue	    ; compare a with memory contents
	bcs  CHECK_IFOVER_1850_2000_6167RPM    ; branch if lower
L1492:	ldx  #REVLMT5_RPMLimiterNormalOnRPM	; load index with value
CHECK_IFOVER_1850_2000_6167RPM:
	ldaa EngineRpm_HB    ; load a with memory contents
	cmpa 0x00,x	    ; compare a with memory at index + value
	bcc  R1493	    ; branch if greater or equal
	cmpa SPDRPM2_EngineSpeedLowLimitToDisableOverspeed    ; compare a with memory contents (data is 77)
	bls  Cutout_TurnFuelBackOn    ; branch if lower or same
	ldaa Temp1	    ; load a with memory contents
	cmpa SPDLML_SpeedLimitFuelShutoffRestore253mph	  ; compare a with memory contents (data is 6e)
	bls  Cutout_TurnFuelBackOn    ; branch if lower or same
R1493:	rts		    ; return from subroutine

DealWithSpecialIdle_SetBasicTiming_MM:
	brset *BitFlags_4f, #b4f_OffIdle, THROTTLE_PRESSED1    ; branch if bit(s) set
	ldaa RICHSA_OpenLoopEnrichFactorWhenSettingBasicTiming	  ; load a with memory contents (data is 1a)
	brset *b45_IPL1, #b45_BadCoolantTemp, L1495	  ; branch if bit(s) set
	ldaa RIDLST_OpenLoopEnrichFactorWhenSettingMinThrottleOpening	 ; load a with memory contents (data is 1a)
	ldab DRBPointer1    ; load b with memory contents
	cmpb #0x14	    ;  -00010100-
	bne  L1494	    ; branch if not equal (not zero)
	ldab DRBPointer2    ; load b with memory contents
	cmpb #0x10	    ;  -00010000-
	beq  L1495	    ; branch if equal (zero)
L1494:	clra		    ; a = 0
L1495:	brclr *Timer_OffThrottleFuelEnrich, #$%11111111, LOAD_FUELENRICHVAR    ; branch if bit(s) clear
	tsta		    ; test a
	bne  LOAD_FUELENRICHVAR    ; branch if not equal (not zero)
	ldaa O2ITIM_TimeO2InhibitedSwitchingRichIdleToClosedLoop    ; load a with memory contents (data is ff)
	staa Timer_O2InhibitSwitchingRichIdleToClosedLoop    ; store a into memory
THROTTLE_PRESSED1:
	clra		    ; a = 0
LOAD_FUELENRICHVAR:
	staa Timer_OffThrottleFuelEnrich    ; store a into memory
	beq  R1496	    ; branch if equal (zero)
	clra		    ; a = 0
	staa Counter_PrimaryAndSecondaryRamp    ; store a into memory
	staa Counter_AdaptiveMem_Erase	  ; store a into memory
R1496:	rts		    ; return from subroutine

CalculatePartThrottleEnrichmentAndSparkScatterFuel_MM:
	ldx  #RPMMAP_SwitchPointForDownUp_FromRpm     ; load index with value
	ldaa EngineRpm_HB    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	cmpa MapValue	    ; compare a with memory contents
	rora ; after the rotate, the carry bit will be in bit 7, value in A will be MAP/2
	ldx  #PTENR_EppPerAmountForIncreasing	 ; load index with value
	anda #0x80	    ; AND a with value -10000000-  this clears out everything from A except for bit7
	bmi  MAPAbove_RPMMAP	    ; branch if minus(hi bit 1) - this only happens when MAP is higher than the lookup value

MAPBelow_RPMMAP:
	inx
	inx                 ; move X pointer to correct value

MAPAbove_RPMMAP:
        staa Temp0	    ; store a into memory - only bit 7 status
	tab		    ; b = a
	eorb Counter_FallingEdgeEPP_MaxFF  ; bit7 has special meaning?
	bpl  Bit7_IsSet	    ; branch if plus (hi bit 0) - branch if bit7 is set in either Counter_EPP or from lookup, but not both

Bit7_IsClear:
        staa Counter_FallingEdgeEPP_MaxFF    ; store a into memory
	ldab Timer_OpenLoopFraction    ; load b with memory contents
	bra  L1506	    ; branch

Bit7_IsSet:
	ldab 0x00,x	    ; load b with PTENR_EppPerAmountForIncreasing (1 or 2)
	sei		    ; disable interrupts
	eora Counter_FallingEdgeEPP_MaxFF
	cba		
	bcs  L1499	    ; branch if lower
	sba		    ; subtract (a=a-b) B = constant value, A =
L1499:	oraa Temp0	    ; OR a with memory contents - only bit7 status
	staa Counter_FallingEdgeEPP_MaxFF    ; store a into memory
	cli		    ; enable interrupts
	ldab Timer_OpenLoopFraction    ; load b with memory contents
	bcs  L1506	    ; branch if lower
	addb 0x01,x	    ; add memory at index + value to b
	bpl  L1500	    ; branch if plus (hi bit 0)
	clrb		    ; b = 0
	tsta		    ; test a
	bpl  L1500	    ; branch if plus (hi bit 0)
	ldab #0x7f	    ; load b with value -01111111-
L1500:	stab Temp0	    ; store b into memory
	ldx  #PTELMT_MultiplierMaxLimitFromRpm	  ; load index with value
	ldaa EngineRpm_HB    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Temp4	    ; store a into memory
	ldx  #PTEADJ_EnrichAdjust_FromMap    ; load index with value
	ldaa MapValue	    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	ldaa Temp4	    ; load a with memory contents
	tstb		
	beq  L1501	    ; branch if equal (zero)
	mul		    ; multiply (d=a*b)
	adca #0x00	    ;  -00000000-
L1501:	tab		    ; b = a
	cmpb Temp0
	bls  SetPTEMaxFlag	    ; branch if lower or same
	brclr *BitFlags_4f, #b4f_PTEisMaxed, StoreTemp0_ToOpenLoopFractionTimer    ; branch if bit(s) clear
	ldab Timer_OpenLoopFraction    ; load b with memory contents
	beq  ClearPTEMaxFlag	    ; branch if equal (zero)
	sba		    ; subtract (a=a-b)
	staa Temp1	    ; store a into memory
	ldaa PTENRD_AmountForDecreasingMultiplier_Negative    ; load a with memory contents (data is ff)
	beq  StoreTemp0_ToOpenLoopFractionTimer	    ; branch if equal (zero)
	nega		    ; negate a (set high bit)
	ldab PTENUM_NumberToReturnToHOTMAP    ; load b with memory contents (data is 0f)
	mul		    ; multiply (d=a*b)
	tsta		    ; test a
	bne  StoreTemp0_ToOpenLoopFractionTimer	    ; branch if not equal (not zero)
	cmpb Temp1	
	bcc  StoreTemp0_ToOpenLoopFractionTimer	    ; branch if greater or equal
ClearPTEMaxFlag:
	bclr *BitFlags_4f, #b4f_PTEisMaxed    ; clear bits

StoreTemp0_ToOpenLoopFractionTimer:
	ldab Temp0	    ; load b with memory contents
	bra  StoreOpenLoopFractionTimer	    ; branch

SetPTEMaxFlag:
	bset *BitFlags_4f, #b4f_PTEisMaxed    ; set bits

StoreOpenLoopFractionTimer:
	stab Timer_OpenLoopFraction    ; store b into memory

L1506:	brclr *BitFlags_4f, #b4f_OffIdle, L1507    ; branch if bit(s) clear
	bne  L1508	    ; branch if not equal (not zero)
L1507:	ldaa MapValue	    ; load a with memory contents
	cmpa BOOSTP_AdjustO2ResponseForPTEWhenMapAboveThis    ; compare a with memory contents (data is ff)
	bcs  LookupInjectorLatency	    ; branch if lower
L1508:	ldaa Counter_PrimaryAndSecondaryRamp    ; load a with memory contents
	bpl  LookupInjectorLatency	    ; branch if plus (hi bit 0)
	clra		    ; a = 0
	staa Counter_PrimaryAndSecondaryRamp    ; store a into memory

LookupInjectorLatency:
	ldaa #0xe2	    ; load a with value -11100010-
	brset *b45_IPL1, #b45_Bad_BatVolts, L1510	; branch if bit(s) set
	ldaa BatteryVolts    ; load a with memory contents
L1510:	ldx  #BATOFF_FuelBatteryOffset	  ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	staa InjectorLatency	; store a into memory
	ldaa BaroPressure    ; load a with memory contents
	ldx  #PWADD_FuelPWModifierFromBaro    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	clra		    ; a = 0
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	stD *Temp0	    ; store D to RAM
	ldaa CoolantTemp    ; load a with memory contents
	cmpa IDLTMP_Use_IDLADD_AboveThisTemp	; compare a with memory contents (data is 8a)
	bls  L1511	    ; branch if lower or same
	brset *BitFlags_50, #b50_IdleSpeedMode, L1511	 ; branch if bit(s) set
	brset *BitFlags_55, #b55_UseSparkScatter, UsingSparkScatterToControlIdle    ; branch if bit(s) set
L1511:	ldd  Temp0	    ; load d (a&b) with memory contents
	stD *SparkScatterFuelStabilizationValue_HB    ; store D to RAM
	rts		    ; return from subroutine

UsingSparkScatterToControlIdle:
	ldd  EngineRpm_HB    ; load d (a&b) with memory contents
	subd TargetIdleSpeed_HB	; d = d - memory contents
	bcc  IDLERPM_TOO_HIGH	 ; branch if greater or equal
	coma
	comb		
	bsr  DIN_ACLRDBOUT_CALCULATE_BASEDON_IDLE_ERROR_ROUTINE    ; call subroutine
	addd Temp0	    ; d = d + memory contents
	stD *SparkScatterFuelStabilizationValue_HB    ; store D to RAM
	rts		    ; return from subroutine

IDLERPM_TOO_HIGH:
	bsr  DIN_ACLRDBOUT_CALCULATE_BASEDON_IDLE_ERROR_ROUTINE    ; call subroutine
	subd Temp0	    ; d = d - memory contents
	coma		
	comb		
	stD *SparkScatterFuelStabilizationValue_HB    ; store D to RAM
	rts		    ; return from subroutine

DIN_ACLRDBOUT_CALCULATE_BASEDON_IDLE_ERROR_ROUTINE:
	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	tsta		    ; test a
	beq  L1512	    ; branch if equal (zero)
	ldab #0xff	    ; load b with value -11111111-
L1512:	tba		    ; a = b
	ldx  #IDLADD_FuelStabilization_FromDeltaRPM    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	clra		    ; a = 0
	rts		    ; return from subroutine

CalculateSumOfAllFuelModifiers_MM:

; *****************************************************************************
; Cold Enrichment Factor Calculation (CNRICH)
;
; 1 + ((CURVEA * ACVDCY/256 + CURVEC * ACVDCY/256 + CURVEB * FCRCVB/256) * 2 +
;     (HMPMUL * HIGHMP)/32) * BAROCP/256
;
; CURVEA, CURVEB, CURVEC Factors:
; X == Engine Temp DegC + 128 ( Engine Temp is scaled between -128C and +128C
;                                                             -198F and +262F
; Y == (Factor - 1) * 128 where the factor is between 1.00 and 2.99
;
; *****************************************************************************

	brset *BitFlags_54, #b54_FuelEngineNotRunning, ClearTemp0ForResultStorage    ; branch if bit(s) set
	ldx  #TMPHLD_TempSwitchPointForCurveAHoldDecay	  ; load index with value
	ldaa CoolantTemp    ; load a with memory contents
	cmpa 0x00,x	    ; compare a with memory at index + value
	bcs  L1513	    ; branch if lower
	inx		    ; increment index (x=x+1)
L1513:	brset *BitFlags_50, #b50_FuelCurveACToggle, L1515	; branch if bit(s) set
	brset *BitFlags_4f, #b4f_O2Valid, L1514    ; branch if bit(s) set
	ldd  KeyOnOrEngineRunningTime	 ; load d (a&b) with memory contents
	asld		    ; shift left (d=d*2)
	bcs  L1514	    ; branch if lower
	asld		    ; shift left (d=d*2)
	bcs  L1514	    ; branch if lower
	cmpa 0x01,x	    ; compare a with memory at index + value
	bcc  L1514	    ; branch if greater or equal
	ldx  #DCYTMC_CurveAColdDecayTime    ; load index with value
	cmpa 0x02,x	    ; compare a with memory at index + value
	bcc  L1515	    ; branch if greater or equal
	bra  ClearTemp0ForResultStorage    ; branch

L1514:	bset *Factor_ACVDCY_CurveACurveCDecayAfterRunModeReached, #$%11111111	 ; set bits
	bset *BitFlags_50, #b50_FuelCurveACToggle	; set bits
L1515:	brset *Counter_MainLoop, #$%00011111, L1516	; branch if bit(s) set
	bra  ClearTemp0ForResultStorage    ; branch

L1516:	ldab Factor_ACVDCY_CurveACurveCDecayAfterRunModeReached    ; load b with memory contents
	subb 0x03,x	
	bcc  L1517	    ; branch if greater or equal
	clrb		    ; b = 0
L1517:	stab Factor_ACVDCY_CurveACurveCDecayAfterRunModeReached    ; store b into memory

ClearTemp0ForResultStorage:
	clra		    ; a = 0
	staa Temp0	    ; store a into memory
	brset *BitFlags_4f, #b4f_FullThrottle, INCLUDE_COOLANTTEMP_ANDIFNOTFLOORED_RPM_COMBINATION    ; branch if bit(s) set
	brset *BitFlags_4f, #b4f_PTEisMaxed, INCLUDE_COOLANTTEMP_ANDIFNOTFLOORED_RPM_COMBINATION    ; branch if bit(s) set
	jsr  AllowForHeatSoakAfterStall    ; call subroutine
	brset *BitFlags_50, #b50_FuelCurveACToggle, L1518	; branch if bit(s) set
	ldx  #CURVEC_FuelColdEnrichmentCurveC	 ; load index with value
	staa Temp1	    ; store a into memory
	jsr  Lookup4ByteTable	 ; call subroutine
	ldab Factor_ACVDCY_CurveACurveCDecayAfterRunModeReached    ; load b with memory contents
	mul		    ; multiply (d=a*b)
	adca #0x00	    ;  -00000000-
	staa Temp0	    ; store a into memory
	ldaa Temp1	    ; load a with memory contents
L1518:	ldx  #CURVEA_FuelColdEnrichmentCurveA	 ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	brclr *BitFlags_50, #b50_FuelCurveACToggle, L1519	; branch if bit(s) clear
	ldab Factor_ACVDCY_CurveACurveCDecayAfterRunModeReached    ; load b with memory contents
	mul		    ; multiply (d=a*b)
	adca #0x00	    ;  -00000000-
L1519:	adda Temp0
	staa Temp0	    ; store a into memory
INCLUDE_COOLANTTEMP_ANDIFNOTFLOORED_RPM_COMBINATION:
	ldaa CoolantTemp    ; load a with memory contents
	ldx  #CURVEB_FuelColdEnrichmentCurveB	 ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	brclr *BitFlags_4f, #b4f_FullThrottle, THROT_NOT_FLOORED3    ; branch if bit(s) clear
	stab Temp1	    ; store b into memory
	ldaa EngineRpm_HB    ; load a with memory contents
	ldx  #FCRCVB_FuelWOTScaleEnrichBFromRpm    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	ldab Temp1	    ; load b with memory contents
	tsta		    ; test a
	beq  IncludePartThrottleEnrichmentIfNotFullThrottle    ; branch if equal (zero)
	mul		    ; multiply (d=a*b)
	tab		    ; b = a
THROT_NOT_FLOORED3:
	clra		    ; a = 0
IncludePartThrottleEnrichmentIfNotFullThrottle:

; *****************************************************************************
; Load Enrichment:
; Cold Load Factor == HIGHMP * HMPMUL/32
; 
; HIGHMP Factors:
; X - Engine Temp
; Y - (% enrichment per Torr/100) * 32 * 5.88 * 256
;
; HMPMUL Factors:
; X - MAP in Torr * 0.17
; Y - MAP in Torr * 0.17
;
; *****************************************************************************

	addb Temp0	    ; b=b+memory contents
	rola		
	asld		    ; shift left (d=d*2)
	stD *Temp0	    ; store D to RAM
	brset *BitFlags_4f, #b4f_FullThrottle, HandleBaroCompForWarmup	  ; branch if bit(s) set
	brset *BitFlags_4f, #b4f_PTEisMaxed, HandleBaroCompForWarmup	; branch if bit(s) set
	ldx  #HIGHM2_ColdLoadFromCoolantTemp2	 ; load index with value
	brset *BitFlags_4f, #b4f_OffIdle, L1520    ; branch if bit(s) set
	ldx  #HIGHMP_ColdLoadFromCoolantTemp	; load index with value
L1520:	ldaa CoolantTemp    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Temp4	    ; store result of lookup
	ldx  #HMPMU2_ColdLoadFromMAP2	; load index with value
	brset *BitFlags_4f, #b4f_OffIdle, L1521    ; branch if bit(s) set
	ldx  #HMPMUL_ColdLoadFromMAP	; load index with value
L1521:	ldaa MapValue	    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	ldaa Temp4	    ; result from coolant temp lookup table
	mul		    ; multiply (d=a*b)
	lsrd		    ; Divide by 32...
	lsrd		    ; 
	lsrd		    ; 
	lsrd		    ; 
	lsrd		    ;
	addd Temp0	    ; d = d + memory contents
	stD *Temp0	    ; store D to RAM
HandleBaroCompForWarmup:
	ldaa BaroPressure    ; load a with memory contents
	ldx  #BAROCP_BaroCompensationOfWarmupFactor_FromBaro	; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	beq  L1522	    ; branch if equal (zero)
	ldY Temp0	    ; load Y index
	jsr  ScaleYbyA	    ; call subroutine
	xgDY		    ; exchange D and Y
	bra  HandleOffThrottleEnrich	; branch

L1522:	ldd  Temp0	    ; load d (a&b) with memory contents
HandleOffThrottleEnrich:
	inca		    ; increment a
	stD *Temp0	    ; store D to RAM
	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	stab BaseFuelModifier	 ; store b into memory
	ldaa ChargeTemp	; load a with memory contents
	ldx  #AIRTMP_FuelEnrichmentFromChargeTemp    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	ldx  #Temp0	    ; load index with value
	ldaa #0x01	    ; load a with value -00000001-
	jsr  ScaleXbyB_addingA_intoD	; call subroutine
	stD *Temp0	    ; store D to RAM
	ldab Timer_OffThrottleFuelEnrich    ; load b with memory contents
	beq  LeanMixtureFromDecel_ThrottleDecreasing	; branch if equal (zero)
	ldaa #0x01	    ; load a with value -00000001-
	jsr  ScaleXbyB_addingA_intoD	; call subroutine
	stD *Temp0	    ; store D to RAM
LeanMixtureFromDecel_ThrottleDecreasing:
	ldaa Factor_DecelLeanoutWhenThrottleDecreasing	  ; load a with memory contents
	beq  LeanMixtureFromDecel_MapDecreasing    ; branch if equal (zero)
	ldY Temp0	    ; load Y index
	jsr  ScaleYbyA	    ; call subroutine
	stY Temp0	    ; store Y index
LeanMixtureFromDecel_MapDecreasing:
	ldaa Factor_DecelLeanoutWhenMAPDecreasing    ; load a with memory contents
	beq  INCLUDE_ADAPTIVE_MEMORY	; branch if equal (zero)
	ldY Temp0	    ; load Y index
	jsr  ScaleYbyA	    ; call subroutine
	stY Temp0	    ; store Y index
INCLUDE_ADAPTIVE_MEMORY:
	clra		    ; a = 0
	brset *BitFlags_4f, #b4f_FullThrottle, L1526	; branch if bit(s) set
	ldab Timer_OpenLoopFraction    ; load b with memory contents
	bne  L1525	    ; branch if not equal (not zero)
	ldab ValueFromAdaptiveMemory	; load b with memory contents
	bmi  L1524	    ; branch if minus(hi bit 1)
L1523:	inca		    ; increment a
L1524:	asrb
	jsr  ScaleXbyB_addingA_intoD	; call subroutine
	stD *Temp0	    ; store D to RAM
	bra  L1526	    ; branch

L1525:	ldab ValueFromAdaptiveMemory	; load b with memory contents
	bpl  L1523	    ; branch if plus (hi bit 0)
L1526:	clra		    ; a = 0
	ldab Counter_PrimaryAndSecondaryRamp    ; load b with memory contents
	brclr *EGRVar2, #bit_bit7, L1527    ; branch if bit(s) clear
	addb ADMEMA_ValueFromAdaptivememoryAdder1    ;	(data is 00)
	bvc  L1527    ; branch if overflow
	ldab #0x7f	    ; load b with value -01111111-
L1527:
	tstb		
	bmi  IncludePumpEff	    ; branch if minus(hi bit 1)
	inca		    ; increment a
IncludePumpEff:
        asrb
	jsr  ScaleXbyB_addingA_intoD	; call subroutine
	stD *Temp0
	ldaa EngineRpm_HB    ; load a with memory contents
	ldx  #PEFTBL_PumpingEfficiency	  ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
; stock PEFTBL Code - only use with stock peftbl template!!!
        beq  LAC5B          ; branch if equal (zero)
        ldY  Temp0	    ; store D to RAM
        jsr  ScaleYbyA      ; call subroutine
        stY SumOfFuelModifiers_HB    ; store Y index
        rts                 ; return from subroutine

LAC5B:  ldd  Temp0          ; load d (a&b) with memory contents
        stD *SumOfFuelModifiers_HB    ; store D to RAM
        rts                 ; return from subroutine

; LAC5B:  xgDY                ; move Y to D (PW value)
; 	brclr *Turbonator_Flags, #Turbonator_Staging, SaveFuelModifier
; 	xgDX		    ; exchange D and X - move D to X
;         ldaa #0x01
;         ldab STGENR_StagingFuelEnrichment
;         jsr  ScaleXbyB_addingA_intoD
; 
; ; 150% PEFTBL code... Argh! Doesn't fucking work!
; ;         ldx  #Temp0
; ;         clra
; ;         tstb
; ;         bmi  LBB98          ; branch if minus(hi bit 1)
; ;         inca                ; increment a
; ; LBB98:  jsr  ScaleXbyB_addingA_intoD    ; call subroutine
; ; ; code added to enrichen the fuel while staging
; ; 	brclr *Turbonator_Flags, #Turbonator_Staging, SaveFuelModifier
; ; 	xgDX		    ; exchange D and X
; ;         ldaa #0x01
; ;         ldab STGENR_StagingFuelEnrichment
; ;         jsr  ScaleXbyB_addingA_intoD
; 
; 
; SaveFuelModifier:
;         stD *SumOfFuelModifiers_HB    ; store D to RAM
;         rts                 ; return from subroutine


; stock PEFTBL Code - only use with stock peftbl template!!!
;         beq  LAC5B          ; branch if equal (zero)
;         ldY Temp0           ; load Y index
;         jsr  ScaleYbyA      ; call subroutine
;         stY SumOfFuelModifiers_HB    ; store Y index
;         rts                 ; return from subroutine
; 
; LAC5B:  ldd  Temp0          ; load d (a&b) with memory contents
;         stD *SumOfFuelModifiers_HB    ; store D to RAM
;         rts                 ; return from subroutine

AllowForHeatSoakAfterStall:
	ldaa CoolantTemp    ; load a with memory contents
	cmpa RUNLMT_MaxAllowableTempFor_RUNTMP	  ; compare a with memory contents (data is a0)
	bcc  R1530	    ; branch if greater or equal
	ldaa EngineRunningTimeBeforeStall    ; load a with memory contents
	ldx  #RUNTMP_ModifierOf_ENGTMP_FromStalltime	; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	adda CoolantTemp
	ldab RUNLMT_MaxAllowableTempFor_RUNTMP	  ; load b with memory contents (data is a0)
	bcs  L1529	    ; branch if lower
	cba		
	bcs  R1530	    ; branch if lower
L1529:	tba		    ; a = b
R1530:	rts		    ; return from subroutine

; OC2 = Wastegate
; OC3 = Injector A
; OC4 = Injector B
; OC5 = Dwell

ACCOUNTFORBATVOLTAGE_LOAD_INJECTOR_DRIVERS_ROUTINE:
	ldaa CPU_TimerControlReg1    ; load a with memory contents
	oraa #0xe8	    ;  -11101000-   set OC2, Clear OC3,4 pins on comapre, ignore OC5   - OC3 = Inject A, OC4
	brclr *BitFlags_55, #b55_InjectorB, TurnOnInjBankB    ; branch if bit(s) clear

TurnOnInjBankA:
        anda #0xfb	    ; AND a with value -11111011- clear OC4 on compare, set all others
	ldx  #CPU_Timer_OC4_InjectorADriver    ; load index with value
	bra  L1532	    ; branch

TurnOnInjBankB:	
        anda #0xef	    ; AND a with value -11101111-  clear OC3 on comapre, set all others
	ldx  #CPU_Timer_OC3_InjectorBDriver    ; load index with value
L1532:	jsr  StoreTCTL1_AndIncrTimers	    ; call subroutine
	stD *Temp7	    ; store D to RAM
	ldab InjectorLatency	; load b with memory contents
	clra		    ; a = 0
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	addd InjectorPulsewidth_HB    ; d = d + memory contents
	bcc  L1533	    ; branch if greater or equal
	ldaa #0xff	    ; load a with value -11111111-
	bra  L1534	    ; branch

L1533:	cmpD #0x0060	    ; compare D -00000000 01100000-   - this is kind of the minimum PW, should this be scaled?
	bcc  L1534	    ; branch if greater or equal
	ldd  #0x0060	    ; load d (a&b) with value -00000000 01100000-
L1534:	brclr *BitFlags_55, #b55_InjectorB, L1535    ; branch if bit(s) clear
	addd CPU_Timer_OC4_InjectorADriver
	std  CPU_Timer_OC4_InjectorADriver
	ldaa CPU_TimerControlReg1    ; load a with memory contents
	oraa #0xec	    ;  -11101100- Clear OC3, set OC2, OC4, ignore OC5
	staa CPU_TimerControlReg1
	bra  L1536	    ; branch

L1535:	addd CPU_Timer_OC3_InjectorBDriver
	std  CPU_Timer_OC3_InjectorBDriver
	ldaa CPU_TimerControlReg1    ; load a with memory contents
	oraa #0xf8	    ;  clear OC4, ignore OC5 
	staa CPU_TimerControlReg1
L1536:	ldd  InjectorPulsewidth_HB    ; load d (a&b) with memory contents
	addd Timer_FuelMonitorOutputTimer_HB    ; d = d + memory contents
	bcc  L1537	    ; branch if greater or equal
	ldd  #0xffff	    ; load d (a&b) with value -11111111 11111111-
L1537:	stD *Timer_FuelMonitorOutputTimer_HB    ; store D to RAM

; 	ldd  InjectorPulsewidth_HB    ; load d (a&b) with memory contents
; 	subd FLWMNC_FuelMonitorCorrection    ;	(data is 0066) = 0.102ms
; 	bcc  L1538	    ; branch if greater or equal
; 	clra		    ; a = 0
; 	clrb		    ; b = 0
; L1538:	lsrd		    ; shift right (d=d/2)
; 	addd CCDFuelOutput_HB    ; d = d + memory contents
; 	bcc  L1539	    ; branch if greater or equal
; 	ldd  #0xffff	    ; load d (a&b) with value -11111111 11111111-
; L1539:	stD *CCDFuelOutput_HB    ; store D to RAM

L1540:	ldd  CPU_TimerCounterRegHigh
	subd Temp7	    ; d = d - memory contents
	cmpD #0x0012        ; compare D -00000000 00010010-
	bcs  L1540	    ; branch if lower
	ldd  PIA2_PortB_DataDirection
	bita #pia2b_InjectorDriverSense	    ;  -00000001-
	bne  L1542	    ; branch if not equal (not zero)
	ldaa CPU_PortA		; load a with memory contents
	anda #CPU_PortA_InjectorB | CPU_PortA_InjectorA 	  ; AND a with value -00110000-
	beq  L1542	    ; branch if equal (zero)
	cmpa #CPU_PortA_InjectorB | CPU_PortA_InjectorA	    ; compare a with value -00110000-
	beq  L1542	    ; branch if equal (zero)
	brset *b45_IPL1, #b45_bit3, L1542	; branch if bit(s) set
	bita #CPU_PortA_InjectorA	    ;  -00010000-
	beq  L1541	    ; branch if equal (zero)
	bset *BitFlags_47, #b47_bit4	; set bits
	bra  L1542	    ; branch

L1541:	bset *BitFlags_47, #b47_bit5	; set bits
L1542:	tstb
	bpl  R1545	    ; branch if plus (hi bit 0)
	jmp  IgnitionFeedOnOffTracking

TurnOffBothInjectors:
	clra		    ; a = 0
	clrb		    ; b = 0
	stD *Timer_FuelMonitorOutputTimer_HB    ; store D to RAM
	;stD *CCDFuelOutput_HB    ; store D to RAM
	ldaa CPU_TimerControlReg1    ; load a with memory contents
	oraa #0xfc	    ;  ignore OC5, set all others
	ldx  #CPU_Timer_OC3_InjectorBDriver    ; load index with value
	bsr  StoreTCTL1_AndIncrTimers	    ; call subroutine
	ldx  #CPU_Timer_OC4_InjectorADriver    ; load index with value
	bra  IncrTimers	    ; branch

StoreTCTL1_AndIncrTimers:
	staa CPU_TimerControlReg1
IncrTimers:
	ldd  CPU_TimerCounterRegHigh
	addd #0x0003    ;  -00000000 00000011-
	std  0x00,x	    ; store d into index plus offset
R1545:	rts		    ; return from subroutine

	.org 0xB600

; B600 EEPROM Memory Block
; The EEPROM is mapped in memory from 0xB600 - 0xB7ff.

; 	.org	0xb600
 LB600 = 0xB600
; 	.chem 3 n LB600 in_desc 0 65535 in Y 0 256 out LB600 Detailed_Description
; B600		.byte	0xff
;
; 	.org	0xb610
 LB610 = 0xB610
; 	.chem 3 n LB610 in_desc 0 65535 in Y 0 256 out LB610 Detailed_Description
; B610		.byte	0xff
;
;	.org	0xb620
 LB620 = 0xB620
; 	.chem 3 n LB620 in_desc 0 65535 in Y 0 256 out LB620 Detailed_Description
; B620		.byte	0xff
;
; 	.org	0xb7e0
 CCDBTV_CCDBatteryVoltsOutput = 0xB7E0
; 	.chem 3 n CCDBusBatteryVoltsOutput in_desc 0 65535 in Y 0 256 out CCDBTV Detailed_Description
; B7E0		.byte	0xff
;
; 	.org	0xb7e1
 LB7E1 = 0xB7E1
; 	.chem 3 n LB7E1 in_desc 0 65535 in Y 0 256 out LB7E1 Detailed_Description
; B7E1		.byte	0xff

	.org 0xB800

CalculatePartThrottleTransientFuel_MM:
	clra		    ; a = 0
	staa Temp2	    ; store a into memory
	staa Temp3	    ; store a into memory
	ldaa Timer_O2InhibitSwitchingRichIdleToClosedLoop    ; load a with memory contents
	beq  L1546	    ; branch if equal (zero)
	deca		    ; decrement a
	staa Timer_O2InhibitSwitchingRichIdleToClosedLoop    ; store a into memory
L1546:	ldaa CoolantTemp    ; load a with memory contents
	ldab MapValue	    ; load b with memory contents
	subb AverageMAPValue    ; b = b-memory contents
	stab Temp0	    ; store b into memory
	bcs  TransFuel_CalculateDecreasingMAPTransientFuel    ; branch if lower (decreasing MAP)
	ldx  #AETIME_EnrichmentTime_FromTemp    ; This is the increasing MAP time constant
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Factor_LeanoutOrEnrichTime_MAP    ; store a into memory
	clra		    ; a = 0
	staa Factor_DecelLeanoutWhenMAPDecreasing    ; store a into memory
	ldaa CONFIG_ConfigurationFlags	  ; load a with memory contents (data is 02)
	bita #cfg_UseTPSTransFuelEarly 	 ;  -00000010-
	beq  TransFuel_CalculateIncreasingMAPTransientFuel    ; branch if equal (zero)
	brset *BitFlags_4f, #b4f_OffIdle, TransFuel_CalculateIncreasingMAPTransientFuel    ; branch if bit(s) set
	jmp  TransFuel_IncludeTPSTransients

TransFuel_CalculateIncreasingMAPTransientFuel:
	ldaa Temp0	    ; delta MAP
	suba MAPTRG_DeltaMapTriggerLevel    ;  (data is 0b)
	bcs  TransFuel_IncludeTPSTransients    ; branch if lower
	cmpa MAPMAX_MaxDeltaMapAllowed	  ; compare a with memory contents (data is ff)
	bcs  L1547	    ; branch if lower
	ldaa MAPMAX_MaxDeltaMapAllowed	  ; load a with memory contents (data is ff)
L1547:	staa Temp1	    ; store a into memory
	ldaa CoolantTemp    ; load a with memory contents
	ldx  #AESLOP_DeltaMAPEnrichmentPT    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	ldaa Temp1	    ; load a with memory contents
	mul		    ; multiply (d=a*b)
	stD *Temp2	    ; store D to RAM
	bra  TransFuel_IncludeTPSTransients    ; branch

TransFuel_CalculateDecreasingMAPTransientFuel:
	ldx  #LMAPTC_TimeConstant	 ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Factor_LeanoutOrEnrichTime_MAP    ; store a into memory
	brset *BitFlags_4f, #b4f_FullThrottle, ClearDecelLOMAPFactor	; branch if bit(s) set
	ldaa EngineRpm_HB    ; load a with memory contents
	cmpa LOTRPM_MinRpmForMapLeanout    ; compare a with memory contents (data is 3e)
	bcs  ClearDecelLOMAPFactor	    ; branch if lower
	ldaa CONFIG_ConfigurationFlags	  ; load a with memory contents (data is 02)
	bita #cfg_ATX		;  -00100000-
	beq  L1548	    ; branch if equal (zero)
	brclr *BitFlags_AIS, #b0c_ATXInGear, ClearDecelLOMAPFactor    ; branch if bit(s) clear
L1548:	brclr *KeyOnOrEngineRunningTime, #$%11111111, ClearDecelLOMAPFactor    ; branch if bit(s) clear
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	cmpD #0x0080    ; compare D -00000000 10000000-
	bcs  ClearDecelLOMAPFactor	    ; branch if lower
	ldaa Temp0	    ; load a with memory contents
	nega		    ; negate a (set high bit)
	ldab Factor_DecelLeanoutWhenMAPDecreasing    ; load b with memory contents
	beq  L1549	    ; branch if equal (zero)
	adda DECHYS_DeltaMapHysteresisonTriggerLevels	 ;  (data is 01)
L1549:	cmpa DECTRG_DeltaMapTriggerForNoIncrementalLeanout    ; compare a with memory contents (data is 02)
	bcs  ClearDecelLOMAPFactor	    ; branch if lower
	cmpa DTRG2_DeltaMapTriggerForMaxLeanout    ; compare a with memory contents (data is 05)
	bcs  IncrementDecelLOMAPFactor	    ; branch if lower
	ldaa DCELTM_O2CNTRInhibitAfterLeanoutDone    ; load a with memory contents (data is 00)
	staa Timer_O2InhibitSwitchingRichIdleToClosedLoop    ; store a into memory
	ldaa CoolantTemp    ; load a with memory contents
	ldx  #DECEL_DecelLeanoutFactorMAP	 ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	bra  StoreDecelLOMAPFactor	    ; branch

IncrementDecelLOMAPFactor:
	tstb
	beq  L1553	    ; branch if equal (zero)
	incb		
	bra  StoreDecelLOMAPFactor	    ; branch

ClearDecelLOMAPFactor:
	clrb		    ; b = 0
StoreDecelLOMAPFactor:
	stab Factor_DecelLeanoutWhenMAPDecreasing    ; store b into memory
L1553:	ldaa Counter_MainLoop	  ; load a with memory contents
	bita #0x07	    ;  -00000111-
	bne  TransFuel_IncludeTPSTransients    ; branch if not equal (not zero)
	ldx  #Block_MAP    ; load index with value
	sei		    ; disable interrupts
	jsr  ProcessMapOrTpsBlockData	 ; call subroutine
	cli		    ; enable interrupts
TransFuel_IncludeTPSTransients:
	ldaa CoolantTemp    ; load a with memory contents
	ldab TpsVolts	    ; load b with memory contents
	subb AverageTPSVolts    ; b = b-memory contents
	stab Temp0	    ; store b into memory
	bcs  TransFuel_CalculateDecreasingTPSTransientFuel    ; branch if lower
	ldx  #THRTCN_EnrichmentTime_FromTemp    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Factor_LeanoutOrEnrichTime_TPS    ; store a into memory
	clra		    ; a = 0
	staa Factor_DecelLeanoutWhenThrottleDecreasing	  ; store a into memory
	ldaa Temp0	    ; load a with memory contents
	suba POSTRG_PositiveTransientTriggerLevel    ;  (data is 03)
	bcs  L1560	    ; branch if lower
	cmpa THRMAX_MaxDeltaTHR    ; compare a with memory contents (data is 26)
	bcs  L1554	    ; branch if lower
	ldaa THRMAX_MaxDeltaTHR    ; load a with memory contents (data is 26)
L1554:	staa Temp1	    ; store a into memory
	ldaa CoolantTemp    ; load a with memory contents
	ldx  #POSSLP_DeltaTPSEnrichment_FromTemp    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	ldaa Temp1	    ; load a with memory contents
	mul		    ; multiply (d=a*b)
	addd Temp2	    ; d = d + memory contents
	stD *Temp2	    ; store D to RAM
	bra  L1560	    ; branch

TransFuel_CalculateDecreasingTPSTransientFuel:
	ldx  #LOTIME_DecelLeanoutTimeConstant_FromTemp    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Factor_LeanoutOrEnrichTime_TPS    ; store a into memory
	brclr *KeyOnOrEngineRunningTime, #$%11111111, TransFuel_ClearLeanOutFactor    ; branch if bit(s) clear
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	cmpD #0x0080    ; compare D -00000000 10000000-
	bcs  TransFuel_ClearLeanOutFactor	    ; branch if lower
	ldaa Temp0	    ; load a with memory contents
	nega		    ; negate a (2's complement)
	ldab Factor_DecelLeanoutWhenThrottleDecreasing	  ; load b with memory contents
	beq  L1555	    ; branch if equal (zero)
	adda LOTHYS_LeanoutDeltaThrottleHysteresis    ;  (data is 03)
L1555:	cmpa LOTTRG_DeltaTriggerForDecelLeanout    ; compare a with memory contents (data is 05)
	bcs  TransFuel_ClearLeanOutFactor	    ; branch if lower
	cmpa LOTRG2_SecondDecelLeanoutTrigger	 ; compare a with memory contents (data is 0a)
	bcs  L1556	    ; branch if lower
	ldaa CoolantTemp    ; load a with memory contents
	ldx  #LOTTHR_DecelLeanoutFactor_FromTemp    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	bra  TransFuel_StoreLeanOutFactor	    ; branch

L1556:	tstb
	beq  L1559	    ; branch if equal (zero)
	incb		
	bra  TransFuel_StoreLeanOutFactor	    ; branch

TransFuel_ClearLeanOutFactor:	
        clrb		    ; b = 0
TransFuel_StoreLeanOutFactor:	
        stab Factor_DecelLeanoutWhenThrottleDecreasing	  ; store b into memory
L1559:	ldaa Counter_MainLoop	  ; load a with memory contents
	bita #0x07	    ;  -00000111-
	bne  L1560	    ; branch if not equal (not zero)
	ldx  #Block_TPS    ; load index with value
	sei		    ; disable interrupts
	jsr  ProcessMapOrTpsBlockData	 ; call subroutine
	cli		    ; enable interrupts
L1560:	brset *BitFlags_4f, #b4f_OffIdle, TransFuel_UseRunningPTEPW	 ; branch if bit(s) set
	ldaa PIA2_PortB_DataDirection	 ; load a with memory contents
	bita #pia2b_OC1Toggle	    ;  -00001000-
	beq  TransFuel_UseRunningPTEPW    ; branch if equal (zero)
	ldaa DesiredNewAisPosition    ; load a with memory contents
	suba CurrentAisPosition
	bcs  TransFuel_UseRunningPTEPW    ; branch if lower
	cmpa POSTIG_MinAisPulseRequireToTriggerEnrichment    ; compare a with memory contents (data is 0d)
	bcs  TransFuel_UseRunningPTEPW    ; branch if lower
	ldd  POSFUL_AisEnrichmentFuelPulse    ;  (data is 004c)
	bra  TransFuel_UseAISPTEPW	; branch

TransFuel_UseRunningPTEPW:
	ldd  Temp2	    ; load d (a&b) with memory contents
TransFuel_UseAISPTEPW:
	stD *Pulsewidth_PartThrottleEnrichment_HB    ; store D to RAM
	rts		    ; return from subroutine

InterruptVector_DistributorSignal:
	clrb		    ; b = 0
	stab ATMOffset	    ; store b into memory
	ldaa DRBPointer1    ; load a with memory contents
	cmpa #0x0a	    ; compare a with value -00001010-
	bne  L1561	    ; branch if not equal (not zero)
	stab DRBPointer1    ; store b into memory
	bra  L1562	    ; branch

L1561:	cmpa #0x13	    ; compare a with value -00010011-
	bne  L1562	    ; branch if not equal (not zero)
	bset *BitFlags_55, #b55_O2Enable    ; set bits
L1562:	ldab SwitchPortAccessReg    ; load b with memory contents
	andb #swp_DistSync	    ;  -00100000-
	stab Temp6	    ; store b into memory
	ldaa #0x10	    ; load a with value -00010000-
	staa CPU_A2DControlReg
	ldd  CPU_TimerInputCapture1_Distributor
	jsr  DetermineNumberOfOverflowsBetweenDistributorPulses_MM    ; call subroutine
Delay256uSec:
	ldd  CPU_TimerCounterRegHigh
	subd CPU_TimerInputCapture1_Distributor
	subd #0x0040    ;  -00000000 01000000-
	bcs  Delay256uSec    ; branch if lower
	ldab #CPU_TIFlag1_IC1Distributor	    ; load b with value -00000100-
	stab CPU_TimerInterruptFlag1	; store b into memory
	ldaa CPU_TimerControlReg2    ; load a with memory contents
	anda #0x30	    ; setup edge trigger 1 to capture both falling and rising edges
	beq  SETTOLOOKFORRISINGEDGE_STARTAD_RETURN	; branch if equal (zero)
	cmpa #0x30	    ; check if set to capture rising and falling edge on IC1
	beq  SETTOLOOKFORRISINGEDGE_STARTAD_RETURN	; branch if equal (zero)
	lsra		
	lsra
	eora CPU_PortA
	bita #CPU_PortA_DistRef	     ;	-00000100-
	beq  DistributorSignalIsWhatWasExpected    ; branch if equal (zero)
SETTOLOOKFORRISINGEDGE_STARTAD_RETURN:
	ldaa CPU_TimerControlReg2    ; load a with memory contents
	oraa #0x10	    ;  set bit 4 to look for rising edge only on 1
	anda #0xdf	    ;  clear bit 5 to look for rising edge only on 1
	staa CPU_TimerControlReg2
	rti		    ; return from interrupt

DistributorSignalIsWhatWasExpected:
	ldaa Counter_SomethingWithDistributor	 ; load a with memory contents
	inca		    ; increment a
	beq  L1563	    ; branch if equal (zero)
	staa Counter_SomethingWithDistributor	 ; store a into memory
L1563:	ldaa PIA2_PortB_ControlRegister    ; load a with memory contents
	bpl  L1564	    ; branch if plus (hi bit 0)
	jsr  IgnitionFeedOnOffTracking	  ; call subroutine
L1564:	ldaa CPU_TimerControlReg2    ; load a with memory contents
	bita #0x10	    ;  check if bit 4 set to look for rising edge only on 1
	bne  Interrupt_HandleDistributorRisingEdge    ; branch if not equal (not zero)
	jmp  Interrupt_HandleDistributorFallingEdge

Interrupt_HandleDistributorRisingEdge:
	ldaa EngineRpm_HB    ; load a with memory contents
	cmpa #0x8e	    ; compare a with value -10001110-
	bcs  ENGINE_RPM_LESS_THAN_4544RPM    ; branch if lower
	brclr *BitFlags_55, #b55_SearchBladeEndRef_INSYNC, SETTOLOOKFOR_FALLINGEDGE_NEXTTIME1    ; branch if bit(s) clear
	ldd  CPU_TimerInputCapture1_Distributor
	subd LastDistributorFallingEdgeTime    ; d = d - memory contents
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	ldab #0x03	    ; load b with value -00000011-
	mul		    ; multiply (d=a*b)
	stab Temp5	    ; store b into memory
	ldd  DistributorFallingEdgePulsewidth_HB    ; load d (a&b) with memory contents
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	tab		    ; b = a
	ldaa Temp5	    ; load a with memory contents
	cba		
	bcc  NORMAL_BLADE_JUST_TRIGGERED_INTERRUPT    ; branch if greater or equal
	bset *BitFlags_55, #b55_DistSync | b55_SearchBladeEndRef_INSYNC    ; set bits
	bra  DIST_SYNC_WENT_TO_ONE_WINDOWBLADE_JUSTCUTTING_REFPICKUP	; branch

NORMAL_BLADE_JUST_TRIGGERED_INTERRUPT:
	bclr *BitFlags_55, #b55_DistSync    ; clear bits
	bra  DIST_SYNC_WENT_TO_ZERO_WINDOWBLADE_JUSTLEAVING_REFPICKUP	 ; branch

ENGINE_RPM_LESS_THAN_4544RPM:
	brset *BitFlags_55, #b55_SearchBladeEndRef_INSYNC, USE_DISTSYNCPICKUP_TOSETPOSITIONBITS    ; branch if bit(s) set
SETTOLOOKFOR_FALLINGEDGE_NEXTTIME1:
	ldab CPU_TimerControlReg2    ; load b with memory contents
	orab #0x20	    ;  set bit 5 to look for falling edge only on 1
	andb #0xef	    ;  set bit 5 to look for falling edge only on 1
	stab CPU_TimerControlReg2    ; store b into memory
	brclr *BitFlags_51, #b51_BladePassedSensor_INSYC3, USE_DISTSYNCPICKUP_TOSETPOSITIONBITS    ; branch if bit(s) clear
	bset *BitFlags_55, #b55_SearchBladeEndRef_INSYNC | b55_InjectorAandB	 ; set bits
	bra  L1567	    ; branch

USE_DISTSYNCPICKUP_TOSETPOSITIONBITS:
	ldab Temp6	    ; load b with memory contents
	ldaa BitFlags_55    ; load a with memory contents
	staa Temp5	    ; store a into memory
	anda #~b55_DistSync	     ; AND a with value -11011111-
	aba		    ; a=a+b
	staa BitFlags_55    ; store a into memory
	eorb Temp5
	bitb #0x20	    ;  -00100000-
	beq  DIST_SYNC_HASNT_CHANGED_REGULARBLADE_CUT_REFPICKUP    ; branch if equal (zero)
	ldab Temp6	    ; load b with memory contents
	beq  DIST_SYNC_WENT_TO_ZERO_WINDOWBLADE_JUSTLEAVING_REFPICKUP	 ; branch if equal (zero)
	bset *BitFlags_55, #b55_SearchBladeEndRef_INSYNC    ; set bits
DIST_SYNC_WENT_TO_ONE_WINDOWBLADE_JUSTCUTTING_REFPICKUP:
	bclr *BitFlags_55, #b55_InjectorAandB	 ; clear bits
	jmp  SETTOLOOKFORRISINGEDGE_STARTAD_RETURN

CAM_POSITION_NOT_INSYNC:
	bclr *BitFlags_55, #b55_SearchBladeEndRef_INSYNC    ; clear bits
	bset *BitFlags_47, #b47_bit1	; set bits
R1566:	rti		    ; return from interrupt

DIST_SYNC_HASNT_CHANGED_REGULARBLADE_CUT_REFPICKUP:
	brclr *BitFlags_55, #b55_InjectorAandB, CAM_POSITION_NOT_INSYNC    ; branch if bit(s) clear
DIST_SYNC_WENT_TO_ZERO_WINDOWBLADE_JUSTLEAVING_REFPICKUP:
	brset *BitFlags_55, #b55_InjectorAandB, ZERO_CAM_POSITION_BITS	  ; branch if bit(s) set
	inc  BitFlags_55
	bra  L1567	    ; branch

ZERO_CAM_POSITION_BITS:
	bclr *BitFlags_55, #b55_InjectorAandB	 ; clear bits
L1567:	brclr *BitFlags_55, #b55_SearchBladeEndRef_INSYNC, R1566    ; branch if bit(s) clear
	ldaa TimerOverflowsBetweenDistPulses	; load a with memory contents
	bne  FORCE_DWELL_TO_ACTIVATE	; branch if not equal (not zero)
	brclr *BitFlags_54, #b54_DisableNormalDwell, TachSignalAndClearKnockSensorCap	 ; branch if bit(s) clear
FORCE_DWELL_TO_ACTIVATE:
	ldaa CPU_TimerControlReg1    ; load a with memory contents
	anda #0xfe	    ; Setup OC5 to clear on successful compare
	staa CPU_TimerControlReg1
	ldaa #0x08	    ; force OC5 compare
	staa CPU_TimerForceCompare
TachSignalAndClearKnockSensorCap:
	ldab PIA2_PortA_DataDirection	 ; load b with memory contents
	andb #0xfb	    ;  -11111011-
	stab PIA2_PortA_DataDirection	 ; store b into memory
	ldd  PIA2_PortB_DataDirection
	anda #~pia2b_KnockCap	    ; AND a with value -11011111-
	staa PIA2_PortB_DataDirection
	tstb
	bpl  SETTOLOOKFOR_FALLINGEDGE_NEXTTIME0    ; branch if plus (hi bit 0)
	jsr  IgnitionFeedOnOffTracking	  ; call subroutine
SETTOLOOKFOR_FALLINGEDGE_NEXTTIME0:
	ldaa EngineRpm_HB    ; load a with memory contents
	cmpa #0x76	    ; compare a with value - [3776rpm]
	bcs  SetTCR2ForFallingEdge	    ; branch if lower
	ldaa #CPU_TIFlag1_OC5Dwell	    ; clear the dwell flag
	bita CPU_TimerInterruptFlag1
	beq  SetTCR2ForFallingEdge	    ; branch if no interrupt flags set
	staa CPU_TimerInterruptFlag1        ; store the flags 
	brclr *BitFlags_55, #b55_SearchBladeEndRef_INSYNC, SetTCR2ForFallingEdge    ; branch if bit(s) clear

; here, add code to prevent ouput if spark cut is desired...
        brclr *Turbonator_Flags, #Turbonator_AllowSpark, SetTCR2ForFallingEdge ; skip the dwell time stuff...

NormalCoilFiring:
; original code
; only reach this if RPM >3776 and INSYNC is set...
        ldaa CPU_TimerControlReg1 ; oops, this was accidentally deleted when fixing the staging limiter code...
	eora #0x01	    ; toggle OC5 to set/clear on next successful compare
	staa CPU_TimerControlReg1
	lsra
	bcc  L1568	    ; branch if bit 1 is clear - OC5 setup to clear on compare - calculate dwell time and store in OC5 timer
	ldd  AntiDwellTime_HB    ; if bit 1 is set, OC5 is setup to set on compare - store antidwell time in OC5 timer
	bra  L1569	    ; branch
;same on time/off time deal as the interrupt routine...
L1568:	ldd  DistributorFallingEdgePulsewidth_HB    ; load d (a&b) with memory contents
	subd AntiDwellTime_HB	    ; d = d - memory contents
L1569:	addd CPU_Timer_OC5_Dwell
	std  CPU_Timer_OC5_Dwell

SetTCR2ForFallingEdge:
	ldaa CPU_TimerControlReg2    ; load a with memory contents
	oraa #0x20	    ; set bit 5 - setup IC1 (dist) for falling edge only
	anda #0xef	    ; clear bit 4 - setup IC1 (dist) for falling edge only
	staa CPU_TimerControlReg2

ContinueRisingInterruptRoutine:
	inc  AdaptiveCellUpdateTimer_IncrementedEveryDistRisingEdge
	inc  Timer_O2ToggleDuration
	ldaa CPU_A2DResults1	; load a with memory contents
	brset *BitFlags_51, #b51_SparkEngineNotRunning, MAYBE_DO_BAROREADING	; branch if bit(s) set
	ldab EngineRpm_HB    ; load b with memory contents
	cmpb #0x2e	    ;  -00101110-
	bcc  GREATER_THAN_1472RPM    ; branch if greater or equal
	ldab TpsVolts	    ; load b with memory contents
	subb MINTHR_LowestSessionTPS	; b = b-memory contents
	bcs  L1571	    ; branch if lower
	cmpb MPLTHR_ThrottleLevelAbove_MINTHR_ToMatureMapLimpin    ; compare b with memory contents (data is 42)
	bcc  GREATER_THAN_1472RPM    ; branch if greater or equal
L1571:	cmpa MAPHIG_MapSensorUpperLimit    ; compare a with memory contents (data is ee)
	bcc  L1572	    ; branch if greater or equal
	cmpa MAPLOW_MapSensorLowerLimit    ; compare a with memory contents (data is 01)
	bcs  L1572	    ; branch if lower
GREATER_THAN_1472RPM:
	brclr *b45_IPL1, #b45_MapStuck | b45_MapBadSignal, GET_AVERAGE_MAP_READING	 ; branch if bit(s) clear
L1572:	jsr  SimulateMapReadingFromTps	  ; call subroutine
	bra  L1573	    ; branch

GET_AVERAGE_MAP_READING:
	adda MapVolts	
	rora		
L1573:	jsr  ConvertMAPVoltsToValue    ; call subroutine
	staa MapValue	    ; store a into memory
	bra  CALC_SPARK_RETARD_BASED_ON_KNOCK_VOLT    ; branch

MAYBE_DO_BAROREADING: ; only happens here if the engine is not running...
	brclr *BitFlags_54, #b54_BaroOkEngineStopped, CALC_SPARK_RETARD_BASED_ON_KNOCK_VOLT    ; branch if bit(s) clear
	bclr *BitFlags_54, #b54_BaroOkEngineStopped    ; clear bits
	jsr  SaveBaroPressure	 ; call subroutine - accA always needs to contain the raw sensor reading or MAP volts...
CALC_SPARK_RETARD_BASED_ON_KNOCK_VOLT:
	ldx  #Cylinder2Retard	 ; load index with value
	ldab BitFlags_55    ; load b with memory contents
	andb #b55_InjectorAandB 	 ;  -00000011-
	eorb #b55_InjectorB	     ;	-00000010-
	abx		    ; add b to index
	ldab 0x00,x	    ; load b with memory at index + value
	ldaa KnockVolts     ; load a with memory contents
	cmpa KnockSensorThreshold    ; compare a with memory contents
	bcc  CHECK_FOR_OVER5PSIBOOST	; branch if greater or equal
	clra		    ; a = 0
	bra  SUM_ADDITIONAL_RETARD    ; branch

CHECK_FOR_OVER5PSIBOOST:
	ldaa BaroPressure    ; load a with memory contents
	adda KNKOFS_DeltaAboveBaroFor_RTRDRT_and_KNKCNT_and_KNKCOR_incremented	  ;  (data is 17)
	cmpa MapValue	    ; compare a with memory contents
	ldaa RTRDRT_KnockRetardRateNoBoost    ; load a with memory contents (data is 06)
	bcc  SUM_ADDITIONAL_RETARD    ; branch if greater or equal
	bset *BitFlags_55, #b55_BoostOver5psi	 ; set bits
	ldaa RTRDRT2_KnockRetardRateInBoost	  ; load a with memory contents (data is 04)
SUM_ADDITIONAL_RETARD:
	aba		    ; a=a+b
	cmpa #0x40	    ; compare a with value -01000000-
	bcs  MAX_RETARD     ; branch if lower
	ldaa #0x3f	    ; load a with value -00111111-
MAX_RETARD:
	ldab MaxRetardFromMAP	 ; load b with memory contents
	cba		
	bcs  STORE_SMALLEST_RETARD_VALUE    ; branch if lower
	tba		    ; a = b
STORE_SMALLEST_RETARD_VALUE:
	staa 0x00,x	
	ldaa TpsVolts	    ; load a with memory contents
	cmpa AverageTPSVolts    ; compare a with memory contents
	bcs  THROTTLE_HAS_DECREASED    ; branch if lower
	ldx  #Block_TPS    ; load index with value
	jsr  ProcessMapOrTpsBlockData	 ; call subroutine
THROTTLE_HAS_DECREASED:
	brset *BitFlags_4f, #b4f_FullThrottle, L1574	; branch if bit(s) set
	ldaa MapValue	    ; load a with memory contents
	cmpa AverageMAPValue    ; compare a with memory contents
	bcs  MAP_HAS_DECREASED0    ; branch if lower
L1574:	ldx  #Block_MAP    ; load index with value
	jsr  ProcessMapOrTpsBlockData	 ; call subroutine
MAP_HAS_DECREASED0:
	ldaa PIA2_PortB_ControlRegister    ; load a with memory contents
	bpl  CheckConditonsToTurnOffInjectors	    ; branch if plus (hi bit 0)
	jsr  IgnitionFeedOnOffTracking	  ; call subroutine
CheckConditonsToTurnOffInjectors:	
        brclr *BitFlags_55, #b55_InjectorA, R1576    ; branch if bit(s) clear
	brset *BitFlags_54, #b54_FuelEngineNotRunning, L1577	; branch if bit(s) set
	brclr *Turbonator_Flags, #Turbonator_FuelOff, CalculateInjectorPulsewidthForEngineRunning	 ; branch if bit(s) clear
	jsr  TurnOffBothInjectors    ; call subroutine
R1576:	rti		    ; return from interrupt

L1577:	jsr  ACCOUNTFORBATVOLTAGE_LOAD_INJECTOR_DRIVERS_ROUTINE    ; call subroutine
	rti		    ; return from interrupt

CalculateInjectorPulsewidthForEngineRunning:
	brset *BitFlags_4f, #b4f_OffIdle, L1578    ; branch if bit(s) set
	ldx  #MAPIDL_FuelBaselineFromMap    ; load index with value
	jsr  Lookup5ByteTable_FromMAP	 ; call subroutine
	bra  L1580	    ; branch

L1578:	brclr *BitFlags_4f, #b4f_FullThrottle, L1579	; branch if bit(s) clear
	ldx  #WOTTBL_FuelFullThrottle	 ; load index with value
	jsr  Lookup5ByteTable_FromMAP	 ; call subroutine
	bra  IncludeSparkScatterFuel	    ; branch

L1579:	ldx  #MAPTBL_FuelPartThrottle	 ; load index with value
	bsr  Lookup5ByteTable_FromMAP	 ; call subroutine
	stD *Temp5	    ; store D to RAM
	ldx  #Temp5	    ; load index with value
	ldab Timer_OpenLoopFraction    ; load b with memory contents
	ldaa #0x01	    ; load a with value -00000001-
	jsr  ScaleXbyB_addingA_intoD	; call subroutine
L1580:	stD *Temp5	    ; store D to RAM
	ldx  #WOTTBL_FuelFullThrottle	 ; load index with value
	bsr  Lookup5ByteTable_FromMAP	 ; call subroutine
	cmpD Temp5	    ; compare D
	bls  IncludeSparkScatterFuel	    ; branch if lower or same
	ldd  Temp5	    ; load d (a&b) with memory contents

IncludeSparkScatterFuel:
	addd SparkScatterFuelStabilizationValue_HB    ; d = d + memory contents
	bpl  INCLUDE_PW_MODIFIERS    ; branch if plus (hi bit 0)
	ldd  Pulsewidth_PartThrottleEnrichment_HB    ; load d (a&b) with memory contents
	bra  HandleTransitionFromStartToRun    ; branch

INCLUDE_PW_MODIFIERS:
	staa Temp7	    ; store a into memory
	tba		    ; a = b
	ldY SumOfFuelModifiers_HB    ; load Y index
	jsr  ScaleYbyA	    ; call subroutine
	stY Temp5	    ; store Y index
	ldaa Temp7	    ; load a with memory contents
	ldab SumOfFuelModifiers_LB    ; load b with memory contents
	mul		    ; multiply (d=a*b)
	addd Temp5	    ; d = d + memory contents
	bcs  LOAD_MAX_INJ_PULSEWIDTH	; branch if lower
	stD *Temp5	    ; store D to RAM
	ldaa Temp7	    ; load a with memory contents
	ldab SumOfFuelModifiers_HB    ; load b with memory contents
	mul		    ; multiply (d=a*b)
	tsta		    ; test a
	bne  LOAD_MAX_INJ_PULSEWIDTH	; branch if not equal (not zero)
	addb Temp5	    ; b=b+memory contents
	bcs  LOAD_MAX_INJ_PULSEWIDTH	; branch if lower
	tba		    ; a = b
	ldab Temp6	    ; load b with memory contents
	addd Pulsewidth_PartThrottleEnrichment_HB    ; d = d + memory contents
	bcc  HandleTransitionFromStartToRun    ; branch if greater or equal
LOAD_MAX_INJ_PULSEWIDTH:
	ldd  #0xffff	    ; load d (a&b) with value -11111111 11111111-
HandleTransitionFromStartToRun:
	brclr *BitFlags_54, #b54_Starting, L1582    ; branch if bit(s) clear
	stD *Temp5	    ; store D to RAM
	ldd  InjectorPulsewidth_HB    ; load d (a&b) with memory contents
	suba Factor_StartFuelDecayIntoRunFuel
	bls  TransitionFromStartToRunComplete	 ; branch if lower or same
	cmpa Temp5	    ; compare a with memory contents
	bhi  L1582	    ; branch if higher
TransitionFromStartToRunComplete:
	clra		    ; a = 0
	staa Factor_StartFuelDecayIntoRunFuel	 ; store a into memory
	ldd  Temp5	    ; load d (a&b) with memory contents
	bclr *BitFlags_54, #b54_Starting    ; clear bits
L1582:	jsr  CallAndReturn1    ; call subroutine
	stD *InjectorPulsewidth_HB    ; store D to RAM
	jsr  ACCOUNTFORBATVOLTAGE_LOAD_INJECTOR_DRIVERS_ROUTINE    ; call subroutine
	rti		    ; return from interrupt

Lookup5ByteTable_FromMAP:
	ldaa MapValue	    ; load a with memory contents

Lookup5ByteTable:
	ldab #0x05	    ; load b with value -00000101-
	cmpa 0x00,x	    ; compare a with memory at index + value
	bhi  L1584	    ; branch if higher
	ldd  0x01,x	
	bra  R1585	    ; branch

L1583:	abx		    ; add b to index
L1584:	cmpa 0x05,x	    ; compare a with memory at index + value
	bhi  L1583	    ; branch if higher
	suba 0x00,x	
	ldY  3, X	    ; load Y indexed to X
	jsr  ScaleYbyA	    ; call subroutine
	xgDY		    ; exchange D and Y
	addd 0x01,x
R1585:	rts		    ; return from subroutine

Interrupt_HandleDistributorFallingEdge:
	ldaa Counter_TimerPastHalfwayBetweenDistPulses	  ; load a with memory contents
	lsra		
	staa TimerOverflowsBetweenDistPulses	; store a into memory
	ldd  CPU_TimerInputCapture1_Distributor
	subd LastDistributorFallingEdgeTime    ; d = d - memory contents
	stD *DistributorFallingEdgePulsewidth_HB    ; store D to RAM
	ldd  CPU_TimerInputCapture1_Distributor
	stD *LastDistributorFallingEdgeTime    ; store D to RAM
	clra		    ; a = 0
	staa Counter_TimerPastHalfwayBetweenDistPulses	  ; store a into memory
	brset *BitFlags_55, #b55_SearchBladeEndRef_INSYNC, FALLING_EDGE_INTERRUPT    ; branch if bit(s) set
	ldaa CPU_TimerControlReg2    ; load a with memory contents
	oraa #0x10	    ; set TCR2 for rising edge on 1
	anda #0xdf	    ; set TCR2 for rising edge on 1
	staa CPU_TimerControlReg2
	rti		    ; return from interrupt

FALLING_EDGE_INTERRUPT:
	ldab PIA2_PortA_DataDirection	 ; load b with memory contents
	orab #pia2a_Tach	    ;  -00000100-
	stab PIA2_PortA_DataDirection	 ; store b into memory
	ldaa Counter_EPP_MaxFF	  ; load a with memory contents
	inca		    ; increment a
	beq  L1586	    ; branch if equal (zero)
	staa Counter_EPP_MaxFF	  ; store a into memory
L1586:	ldab Counter_FallingEdgeEPP_MaxFF    ; load b with memory contents
	asld		    ; shift left (d=d*2)
	addb #0x02	    ;  -00000010-
	bcs  L1587	    ; branch if lower
	lsrd		    ; shift right (d=d/2)
	stab Counter_FallingEdgeEPP_MaxFF    ; store b into memory
L1587:	clra		    ; a = 0
	ldab TimerOverflowsBetweenDistPulses	; load b with memory contents
	beq  HandleFuelStartRunStartTransfer	; branch if equal (zero)
	bset *BitFlags_54, #b54_FuelEngineNotRunning | b54_Starting | b54_DisableNormalDwell	; set bits
	staa Timer_NormalDwell	  ; store a into memory
	bra  L2591    ; branch

HandleFuelStartRunStartTransfer:
	ldab DistributorFallingEdgePulsewidth_HB    ; load b with memory contents
	cmpb RNFPRD_FuelStartRunTransferPointRpm    ; compare b with memory contents (data is 30) --> 625 rpm
	bcc  RpmBelowStartRunTransfer	 ; branch if greater or equal
	brclr *BitFlags_54, #b54_FuelEngineNotRunning, L1589	; branch if bit(s) clear
	bclr *BitFlags_54, #b54_FuelEngineNotRunning | b54_JustStarted	  ; clear bits
	staa KeyOnOrEngineRunningTime	 ; store a into memory
	staa Counter_MainLoop	  ; store a into memory
	staa Pulsewidth_PartThrottleEnrichment_HB    ; store a into memory
	staa Pulsewidth_PartThrottleEnrichment_LB    ; store a into memory
	staa ATMOffset	    ; store a into memory
	ldaa AISDLY_DelayFromStartRunThatAisFeedbackDisabled	; load a with memory contents (data is 2d)
	staa Timer_CountdownFromStartRunForAisFeedback	  ; store a into memory
	ldaa AdaptiveRetardIndex    ; load a with memory contents
	suba ARSUBC_AdaptiveRetardFactorSubtract    ;  (data is 40)
	bcc  L1588	    ; branch if greater or equal
	clra		    ; a = 0
L1588:	staa AdaptiveRetardIndex    ; store a into memory
	bra  L1589	    ; branch

RpmBelowStartRunTransfer:
	cmpb STFPRD_FuelRunStartTransferPointRpm    ; compare b with memory contents (data is 41) --> 460 rpm
	bcs  L1589	    ; branch if lower
	bset *BitFlags_54, #b54_FuelEngineNotRunning | b54_Starting    ; set bits
L1589:	ldaa #0xff	    ; load a with value -11111111-
	cmpb SKAPRD_SparkImmediateSwitchToRunAboveThisRpm    ; compare b with memory contents (data is 24) --> 833 rpm
	bcs  ENGINE_IDLING_FASTERTHAN_813RPM	; branch if lower
	cmpb STRNTR_SparkStartRunTransferPointRpm    ; compare b with memory contents (data is 31) -->612 rpm
	bcs  ENGINE_IDLING_BETWEEN598_813RPM	; branch if lower
	brclr *BitFlags_54, #b54_DisableNormalDwell, L1590    ; branch if bit(s) clear
	clra		    ; a = 0
	staa Timer_NormalDwell	  ; store a into memory
L1590:	cmpb RNSTTR_SparkRunStartTransferPointRpm    ; compare b with memory contents (data is 47) --> 422 rpm
	bcs  L2591    ; branch if lower
	bset *BitFlags_54, #b54_DisableNormalDwell    ; set bits
	bra  L2591    ; branch

ENGINE_IDLING_BETWEEN598_813RPM:
	ldaa Timer_NormalDwell	  ; load a with memory contents
	inca		    ; increment a
	beq  L1591	    ; branch if equal (zero)
ENGINE_IDLING_FASTERTHAN_813RPM:
	staa Timer_NormalDwell	  ; store a into memory
	ldx  #SRTIME_SparkEPPsNeededToBeAboveSR_Hot    ; load index with value
	ldab SRTMTP_SparkTempSwitchPointFor_SRTIME    ; load b with memory contents (data is b0)
	cmpb CoolantTemp
	bcs  SETTOLOOKFOR_RISINGEDGE_AND_CALCULATE_DWELL	; branch if lower
	inx		    ; increment index (x=x+1)
SETTOLOOKFOR_RISINGEDGE_AND_CALCULATE_DWELL:
	cmpa 0x00,x	    ; compare a with memory at index + value
	bcs  L2591	; branch if lower
L1591:	bclr *BitFlags_54, #b54_DisableNormalDwell    ; clear bits
L2591:	ldaa CPU_TimerControlReg2    ; load a with memory contents
	oraa #0x10	    ; set TCR2 for rising edge on 1
	anda #0xdf	    ; set TCR2 for rising edge on 1
	staa CPU_TimerControlReg2

; updated dwell calculation at the advance lookup routine
LCE04:  ldd   DistributorFallingEdgePulsewidth_HB    ; load D (A&B) with memory contents
        subd  DwellTime_HB
        bls   UseMaxDwell         ; branch if lower or same
        cpd   MINADW_MinAntiDwellPeriod       ;  -00000001 10010000-
        bcc   StoreAntiDwell         ; branch if greater or equal
UseMaxDwell:
        ldd   MINADW_MinAntiDwellPeriod       ; load D (A&B) with value -00000001 10010000-
StoreAntiDwell:  
        std   AntiDwellTime_HB    ; store D (A&B) into memory

	brset *BitFlags_51, #b51_SparkEngineNotRunning, L1596	 ; branch if bit(s) set
	ldaa CPU_A2DResults1	; load a with memory contents
	tab		    ; b = a
	suba MapVolts
	stab MapVolts	    ; store b into memory
	bcc  L1594	    ; branch if greater or equal
	nega		    ; negate a (set high bit)
L1594:	cmpa MPDELT_DeltaMapThatChecksGood    ; compare a with memory contents (data is 01)
	bcc  L1595	    ; branch if greater or equal
	brset *b45_IPL1, #b45_MapStuck, L1595    ; branch if bit(s) set
	brset *BitFlags_54, #b54_BigMapChange, L1595	; branch if bit(s) set
	ldd  EngineRpm_HB    ; load d (a&b) with memory contents
	cmpD MPRPML_DisableMapCheckUnderThisRpm_600    ; compare D (data is 12)
	bcs  L1595	    ; branch if lower
	cmpD MPRPMH_DisableMapCheckAboveThisRpm_1500	; compare D (data is 2e)
	bcc  L1595	    ; branch if greater or equal
	ldaa MapVolts	    ; load a with memory contents
	cmpa MPDAGL_DisableMapCheckBelowThisMap    ; compare a with memory contents (data is 0a)
	bcs  L1595	    ; branch if lower
	cmpa MPDAGH_DisableMapCheckAboveThisMap    ; compare a with memory contents (data is 56)
	bcc  L1595	    ; branch if greater or equal
	bset *BitFlags_47, #b47_MapOK	 ; set bits
L1595:	bclr *BitFlags_54, #b54_BigMapChange	; clear bits
L1596:	ldaa TimerOverflowsBetweenDistPulses	; load a with memory contents
	bne  SetupDwellToClearWhenTimeMatches	 ; branch if not equal (not zero)
	brclr *BitFlags_54, #b54_DisableNormalDwell, ReadKnockSensorAndRecalcSparkPosition    ; branch if bit(s) clear

SetupDwellToClearWhenTimeMatches:
; this only runs if b54_DisableNormalDwell is set or the RPM is too low (TimerOverflowsBetweenDistPulses>0)...

        ldaa CPU_TimerControlReg1
	oraa #0x03	    ;  set OC5 to 'set' on sucessful compare
	staa CPU_TimerControlReg1

ClearKnockVolts:
	clra		    ; a = 0
	staa KnockVolts     ; store a into memory
	jmp  ForceDwellOutputChange

ReadKnockSensorAndRecalcSparkPosition:
	ldaa #0x06	    ; load a with value -00000110-
	staa CPU_A2DControlReg
	ldx  #Cylinder2Retard	 ; load index with value
	ldab BitFlags_55    ; load b with memory contents
	andb #b55_InjectorAandB 	 ;  -00000011-
	abx		    ; add b to index
	ldaa CalculatedSparkAdvance    ; load a with memory contents
	suba 0x00,x
	bcc  L1597	    ; branch if greater or equal
	clra		    ; a = 0
L1597:	staa Temp5	    ; store a into memory
	bclr *BitFlags_55, #b55_UseSparkScatter    ; clear bits
	jsr  HandleSparkScatter    ; call subroutine
	ldaa #0x10	    ; load a with value -00010000-
	ldab CPU_A2DResults1	; load b with memory contents
	staa CPU_A2DControlReg
	stab KnockVolts     ; store b into memory
	ldaa Temp5	    ; load a with memory contents

IncludeAntiLag:
        ; re-routed this jump to use the anti-lag lookup value
        jsr  CalculateSparkCutandAntiLagRetard_Routine    ; call subroutine

        staa Temp5	    ; store a into memory
        staa FinalAdvanceActual
        
; this code calculates the dwell timer value based on the desired ignition timing...

	ldaa #0xa6	    ; 0xa6 = 83deg - this is the angle between the rising edge and falling edge; falling edge should be at TDC;
	suba Temp5          ; temp5 contains the total advance - cyl#retard
	ldab #0xb6	    ; 71% is the conversion from degrees to percent - 64/90 = 0.711
	mul		    ; multiply (d=a*b)
	adca #0x00	    ; A now contains the position in scaled degrees from the current edge to ignition firing
	ldY DistributorFallingEdgePulsewidth_HB    ; load Y index
	jsr  ScaleYbyA	    ; call subroutine
	xgDY		    ; D now contains the position in time degrees from the current edge to ignition firing
	addd LastDistributorFallingEdgeTime    ; d = d + memory contents
	stD *Temp6	    ; Temp6/D now contain the position in time degrees from the current system time to ignition firing
	addd AntiDwellTime_HB	    ; add the anti-dwell time
	subd DistributorFallingEdgePulsewidth_HB    ; subtract the FE PW to get the system time to power the coil 'ON' (DwellStart)
	std  CPU_Timer_OC5_Dwell
        
; here, add code to prevent ouput if spark cut is desired...
        brclr *Turbonator_Flags, #Turbonator_AllowSpark, NormalCoilOffTimeLoad ; skip TCR1 stuff if spark is off

NormalCoilOnTimeLoad:
        ldab CPU_TimerControlReg1
	orab #0x03	    ;  setup OC5 to set ouput on compare
	stab CPU_TimerControlReg1    ; store b into memory
	ldx  DistributorFallingEdgePulsewidth_HB
	cpx  #0x3c00	    ; ~977rpm
	bcc  SetBitToClearKnockCap	    ; branch if greater or equal
; special dwell time setup for low RPM only...
	ldd  CPU_Timer_OC5_Dwell
	subd #0x0040        ; 64uS
	subd CPU_TimerCounterRegHigh
	bpl  SetBitToClearKnockCap	    ; branch if plus (hi bit 0)
	ldaa #0x08	    ; force compare of OC5
	staa CPU_TimerForceCompare
	ldd  Temp6	    ; load d (a&b) with memory contents
	std  CPU_Timer_OC5_Dwell
	ldaa #CPU_TIFlag1_OC5Dwell	    ; clear the Dwell flag
	staa CPU_TimerInterruptFlag1

NormalCoilOffTimeLoad:
        ldaa CPU_TimerControlReg1
	anda #0xfe	    ; setup OC5 to clear output on compare
	staa CPU_TimerControlReg1

        ; not sure if this will help or not, seems to work as-is
        brclr *Turbonator_Flags, #Turbonator_AllowSpark, ForceDwellOutputChange ; ensure coil is off if cutting spark

	ldd  CPU_Timer_OC5_Dwell
	subd CPU_TimerCounterRegHigh
	bpl  SetBitToClearKnockCap	    ; branch if plus (hi bit 0)

ForceDwellOutputChange:
	ldaa #0x08	    ; force output compare on 5
	staa CPU_TimerForceCompare

SetBitToClearKnockCap:
	ldd  PIA2_PortB_DataDirection ; ldaa  PIA2_PortB_ControlRegister - this checks the IRQD flag. Cleared by a read of the output register.
	oraa #pia2b_KnockCap	    ;  -00100000-
	staa PIA2_PortB_DataDirection
	tstb
	bpl  R1600	    ; branch if plus (hi bit 0) --> branch if the IRQ Flag in the PIA chip is cleared by the knock cap read.
	jsr  IgnitionFeedOnOffTracking	  ; call subroutine
R1600:	rti		    ; return from interrupt


Interrupt_Software:
	inc  INTERRUPT_COUNTER_VAR
Interrupt_XIRQ:
	inc  INTERRUPT_COUNTER_VAR
Interrupt_COPFail:
	inc  INTERRUPT_COUNTER_VAR
Interrupt_PulseAccumulatorOverflow:
	inc  INTERRUPT_COUNTER_VAR
Interrupt_BadOp:
	inc  INTERRUPT_COUNTER_VAR
Interrupt_SoftwareFail:
	inc  INTERRUPT_COUNTER_VAR
Interrupt_TimerInputCapture3:
	inc  INTERRUPT_COUNTER_VAR
Interrupt_TimerOutputCapture3:
	inc  INTERRUPT_COUNTER_VAR
Interrupt_TimerOutputCapture4:
	inc  INTERRUPT_COUNTER_VAR
Interrupt_PulseAccumulatorInputEdge:
	sei		    ; disable interrupts
	inc  INTERRUPT_COUNTER_VAR
	lds  #0x00ff	     ;	-00000000 11111111-
	jsr  SetupSystemRegisters    ; call subroutine
	bcc  L1601	    ; branch if greater or equal
	jmp  Stop_Routine

L1601:	ldd  #0xe000	    ; load d (a&b) with value -11100000 00000000-
	staa PIA2_PortB_DataDirection
	stab PIA2_PortB_ControlRegister    ; store b into memory
	ldd  #0xf03d	    ; load d (a&b) with value -11110000 00111101-
	staa PIA2_PortB_DataDirection
	stab PIA2_PortB_ControlRegister    ; store b into memory
	ldaa #b0c_bit1		; load a with value -00000010-
	staa BitFlags_AIS    ; store a into memory
	ldd  #0xaaa5	    ; load d (a&b) with value -10101010 10100101-
	cmpD L0000	    ; compare D
	beq  L1604	    ; branch if equal (zero)
	decb
	stab L0001	    ; store b into memory
	bra  L1604	    ; branch

Interrupt_RealTime:
	sei		    ; disable interrupts
	clr  INTERRUPT_COUNTER_VAR    ; zero byte at memory location
	lds  #L00FF	    ;  -00000000 11111111-
	jsr  SetupSystemRegisters    ; call subroutine
	bcc  L1602	    ; branch if greater or equal
	jmp  Stop_Routine

L1602:	ldd  #0xe000	    ; load d (a&b) with value -11100000 00000000-
	staa PIA2_PortB_DataDirection
	stab PIA2_PortB_ControlRegister    ; store b into memory
	ldd  #0xf03d	    ; load d (a&b) with value -11110000 00111101-
	staa PIA2_PortB_DataDirection
	stab PIA2_PortB_ControlRegister    ; store b into memory
	ldx  #0xaaa5	    ; load index with value
	ldd  L0000	    ; load d (a&b) with memory contents
	cmpD #0x5a5a	    ; compare D -01011010 01011010-
	beq  L1603	    ; branch if equal (zero)
	jsr  CountRamValuesFrom02to2e    ; call subroutine
	ldx  #0xaaa5	    ; load index with value
	cmpD L0000	    ; compare D
	beq  L1603	    ; branch if equal (zero)
	ldx  #0x0000	    ; load index with value
L1603:	stx  L0000	    ; store index into memory
L1604:	ldaa #0x0c          ; this needs to be 0c for DRB serial routine to work, (int disable)
        ldab BAUDHI_DRBBaudRateHi
L2604: 	staa CPU_SerialControl2
	stab CPU_SerialBaudRate    ; store b into memory
        clra		    ; a = 0
	staa CPU_SerialControl1
	bclr *BitFlags_AIS, #b0c_bit6 | b0c_UseAIS | b0c_ATXInGear | b0c_ATXChngGear    ; clear bits
	ldx  #0x002f    ; load index with value
	ldaa #pia1b_BaroReadSolenoid | pia1b_EmissionLight | pia1b_bit3  ; load a with value -00111000-
	staa PIA1_PortB_ControlRegister
	ldd  L0000	    ; load d (a&b) with memory contents
	cmpD #0xaaa5	    ; compare D -10101010 10100101-
	beq  L1605	    ; branch if equal (zero)
	ldaa MTHRMX_ValueOf_MINTHR_WhenBatteryDisconnected    ; load a with memory contents (data is 5c)
	staa MINTHR_LowestSessionTPS	; store a into memory
	bclr *BitFlags_AIS, #b0c_bit0 | b0c_bit1    ; clear bits
	bset *BitFlags_AIS, #b0c_UseAIS    ; set bits
	ldab #0xdf	    ; load b with value -11011111-
	stab CurrentAisPosition    ; store b into memory
	ldaa #0x80	    ; load a with value -10000000-
	staa Timer_DacalCountdown	    ; store a into memory
	staa DCCOR1_AdaptiveWastegateCellBelowMAPPT    ; store a into memory
	staa DCCOR2_AdaptiveWastegateCellToDCRPM1    ; store a into memory
	staa DCCOR3_AdaptiveWastegateCellToDCRPM2    ; store a into memory
	staa DCCOR4_AdaptiveWastegateCellToDCRPM3    ; store a into memory
	staa DCCOR5_AdaptiveWastegateCellAboveDCRPM3	 ; store a into memory
	jsr  ERASE_ERROR_CODES	  ; call subroutine
	ldx  #0x000e    ; load index with value -- fixed, was 0x000d (why was it wrong?)
L1605:	clrb		    ; b = 0
	stab CPU_A2DControlReg	  ; store b into memory
	ldaa INTERRUPT_COUNTER_VAR    ; load a with memory contents
ZeroRamFrom0EtoFE:
	stab 0x00,x
	inx		    ; increment index (x=x+1)
	cpx  #L00FF	    ;  -00000000 11111111-
	bls  ZeroRamFrom0EtoFE	  ; branch if lower or same
	staa INTERRUPT_COUNTER_VAR    ; store a into memory
	ldaa CPU_A2DResults1	; load a with memory contents

; this value is #0x34 in the T2 code, why?

	ldab #0x14	    ; load b with value -00010100-
	stab CPU_A2DControlReg	  ; store b into memory
	staa MapVolts	    ; store a into memory
	jsr  SaveBaroPressure	 ; call subroutine
	staa MapValue	    ; store a into memory
	staa AverageMAPValue    ; store a into memory
	ldd  #0xff0c	    ; load d (a&b) with value -11111111 00001100-
	staa PIA1_PortB_DataDirection
	stab PIA2_PortA_DataDirection	 ; store b into memory
	ldd  #0x043d	    ; load d (a&b) with value -00000100 00111101-
	staa PIA2_PortA_ControlRegister
	stab PIA1_PortB_ControlRegister    ; store b into memory
	ldab #0x14	    ; load b with value -00010100-
L1606:	jsr  L1609	    ; call subroutine
	decb
	bne  L1606	    ; branch if not equal (not zero)
	ldab #pia1a_PartThrotUnlock	     ; load b with value -00000100-
	stab PIA1_PortA_ControlRegister    ; store b into memory
	ldaa PIA1_PortA_DataDirection	 ; load a with memory contents
	bita #pia1a_ASDRelay	    ;  -00100000-
	bne  L1607	    ; branch if not equal (not zero)
	bset *BitFlags_51, #b51_ASDon	 ; set bits
L1607:	clra		    ; a = 0
	staa PIA1_PortA_ControlRegister
	deca		    ; decrement a
	staa PIA1_PortA_DataDirection
	stab PIA1_PortA_ControlRegister    ; store b into memory
	staa PIA1_PortA_DataDirection
	staa PIA1_A_Buffer    ; store a into memory
	clr  CPU_PortD		; zero byte at memory location
	ldd  #0x3854	    ; load d (a&b) with value -00111000 01010100-
	staa CPU_PortD_DataDirection
	ldaa CPU_SerialPeripheralStatus    ; load a with memory contents
	stab CPU_SerialPeripheralControl    ; store b into memory

        bset *Turbonator_Flags, #Turbonator_AllowSpark  ; to allow spark by default
        clr  Counter_SparkCut
        bset  *Pattern_SparkCut, #bit_all ; set all bits to ensure cylidner firing

	jsr  BYTE_MODE_SERIAL_CODE_DOWNLOAD_ROUTINE    ; call subroutine <-- not needed here...
        ldaa BAUDLO_DRBBaudRateLo  ; added for serial interrupt routine... (RCL)
L2607:	staa CPU_SerialBaudRate
	bsr  ResetCopTimer    ; call subroutine
	ldaa CPU_A2DResults1	; load a with memory contents
	cmpa #0x40	    ; compare a with value -01000000-
	bcc  L1608	    ; branch if greater or equal
	ldab PIA2_PortB_DataDirection	 ; load b with memory contents
	andb #~pia2b_CoolantTempRange	    ;  -01111111-
	stab PIA2_PortB_DataDirection	 ; store b into memory
L1608:	bset *BitFlags_2d, #bit_tophalf    ; set bits
	ldab BitFlags_2d    ; load b with memory contents
	andb #b2d_both		;  -00000011-
	ldx  #AISTEP_BitPatternForAisControl	; load index with value
	abx		    ; add b to index
	ldaa 0x00,x	    ; load a with memory at index + value
	oraa #0xf0	    ;  -11110000-
	staa PIA1_PortB_DataDirection
	bsr  ResetCopTimer    ; call subroutine
	bset *BitFlags_AIS, #b0c_bit7 | b0c_bit4    ; set bits
	ldd  #0xceff	    ; load d (a&b) with value -11001110 11111111-
	staa CPU_TimerInterruptMask1
	stab CPU_TimerInterruptFlag1	; clear all flags
	stab Counter_TimerPastHalfwayBetweenDistPulses	  ; store b into memory
	stab TimerOverflowsBetweenDistPulses	; store b into memory
	stab Counter_TimerRegHalfOverflowBetweenSpeedoPulses	; store b into memory
	stab TimerOverflowsBetweenSpeedoPulses	  ; store b into memory
	stab Factor_ACVDCY_CurveACurveCDecayAfterRunModeReached    ; store b into memory
	ldaa BitFlags_AIS    ; load a with memory contents
	tab		    ; b = a
	andb #0x03	    ;  -00000011-
	cmpb #0x02	    ;  -00000010-
	bne  SetupSystemAndGoToMainLoop    ; branch if not equal (not zero)
	ldd  #0x0aff	    ; load d (a&b) with value -00001010 11111111-
	staa DRBPointer1    ; store a into memory
	stab DRBPointer2    ; store b into memory
	ldd  #0xf1bf	    ; load d (a&b) with value -11110001 10111111-
	staa LastDistributorFallingEdgeTime    ; store a into memory
	bra  L1610	    ; branch

ResetCopTimer:
	ldd  #0x55aa	    ; code to reset COP timer
	staa CPU_ArmResetCopTimerReg
	stab CPU_ArmResetCopTimerReg	; store b into memory
L1609:	ldaa PIA2_PortB_ControlRegister    ; load a with memory contents
	eora #pia2b_OC1Toggle	       ; XOR a with value -00001000-
	staa PIA2_PortB_ControlRegister
	rts		    ; return from subroutine

SetupSystemAndGoToMainLoop:
	inca		    ; increment a
	staa BitFlags_AIS    ; store a into memory
	ldab #0xdf	    ; load b with value -11011111-
	ldaa L0001	    ; load a with memory contents
	cmpa #0xa4	    ; compare a with value -10100100-
	bne  L1610	    ; branch if not equal (not zero)
	orab #pia1a_ASDRelay	    ;  -00100000-
L1610:	stab PIA1_PortA_DataDirection	 ; store b into memory
	stab PIA1_A_Buffer    ; store b into memory
	ldaa #0x03	    ; load a with value -00000011-
	staa Timer_DelayBeforeUpdating_MINTHR	 ; store a into memory
	ldd  #0x0c28	    ; load d (a&b) with value -00001100 00101000-
	staa BitFlags_4f    ; store a into memory b4f_PartThrottle | b4f_O2Rich
	ldaa CPU_PortA		; load a with memory contents
	bita #CPU_PortA_DistRef	     ;	-00000100-
	bne  L1611	    ; branch if not equal (not zero)
	ldab #0x18	    ; set TCR2 for rising edge on 1, falling edge on 2
L1611:	stab CPU_TimerControlReg2    ; store b into memory
	bset *BitFlags_54, #b54_FuelEngineNotRunning | b54_Starting | b54_DisableNormalDwell   ; set bits
	ldaa #b50_StayOpenLoop | b50_OpenLoop	       ; load a with value -00010100-
	staa BitFlags_50    ; store a into memory
	bsr  ResetCopTimer    ; call subroutine
	ldx  #0x074b	    ; load index with value
L1612:	ldaa SwitchPortAccessReg    ; load a with memory contents
	bita #swp_B1Volt	  ;  -00000001-
	bne  L1613	    ; branch if not equal (not zero)
	dex		    ; decrement index (x=x-1)
	bne  L1612	    ; branch if not equal (not zero)
L1613:	staa StartupSwitchMirror1    ; store a into memory
	staa StartupSwitchMirror2    ; store a into memory
	bsr  ResetCopTimer    ; call subroutine
	ldab #0x14	    ; load b with value -00010100-
	stab CPU_A2DControlReg	  ; store b into memory
L1614:	ldaa CPU_A2DControlReg	  ; load a with memory contents
	bpl  L1614	    ; branch if plus (hi bit 0)
	ldaa CPU_A2DResults4	; load a with memory contents
	staa AmbientAirTempVolts    ; store a into memory
	ldd  CPU_A2DResults1
	stD *RawCoolantTempVolts    ; B goes into 'RawChargeTempVolts'
	stab ChargeTemp	; store b into memory
	ldab #0x10	    ; load b with value -00010000-
	stab CPU_A2DControlReg	  ; store b into memory
	ldx  #TMPTL2_TempForHotScaleA2D    ; load index with value
	ldab PIA2_PortB_DataDirection	 ; load b with memory contents
	bpl  ConvertCoolantRawReadingToTemperature    ; branch if plus (hi bit 0)
	ldx  #TMPTL1_TempForColdScaleFromA2D	; load index with value
ConvertCoolantRawReadingToTemperature:
	jsr  Lookup4ByteTable	 ; call subroutine
	staa CoolantTemp    ; store a into memory
	ldab AmbientAirTempVolts    ; load b with memory contents
	cmpa #0xa6	    ; compare a with value -10100110-
	bcc  L1615	    ; branch if greater or equal
	cmpb #0x99	    ;  -10011001-
	bcs  L1615	    ; branch if lower
	ldab #0x40	    ; load b with value -01000000-
	stab Timer_RadSteamingCountdown    ; store b into memory
L1615:	cmpa TTEMPL_TstatDiagnosticsMinTempToArmDiagnosticsAtStartup	; compare a with memory contents (data is 63)
	bcs  L1616	    ; branch if lower
	cmpa TTEMPH_TstatDiagnosticsMaxTempToArmDiagnosticsAtStartup	; compare a with memory contents (data is e4)
	bcc  L1616	    ; branch if greater or equal
	inc  Timer_ThermostatDiagnostics
L1616:	ldx  #PRSHOT_KeyOnPrimePW    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	ldab #0xfa	    ; load b with value -11111010-
	mul		    ; multiply (d=a*b)
	stD *InjectorPulsewidth_HB    ; store D to RAM
	ldaa CPU_A2DResults2	; load a with memory contents
	staa BatteryVolts    ; store a into memory
	ldaa #b55_InjectorAandB 	 ; load a with value -00000011-
	staa BitFlags_55    ; store a into memory
	jsr  ACCOUNTFORBATVOLTAGE_LOAD_INJECTOR_DRIVERS_ROUTINE    ; call subroutine
	ldaa #b55_InjectorA | b55_WastegateDC	       ; load a with value -01000001-
	staa BitFlags_55    ; store a into memory
	jsr  ACCOUNTFORBATVOLTAGE_LOAD_INJECTOR_DRIVERS_ROUTINE    ; call subroutine
	ldd  CPU_A2DResults3
	stD *RawAirFuelSensInput    ; B goes into 'TPSVolts_11msUpdate'
	stab TpsVolts	    ; store b into memory
	stab AverageTPSVolts    ; store b into memory
	ldaa MINTHR_LowestSessionTPS	; load a with memory contents
	adda MININC_Amount_MINTHR_IsIncreasedAtKeyOnOnly    ;  (data is 03)
	cmpa MTHRMX_ValueOf_MINTHR_WhenBatteryDisconnected    ; compare a with memory contents (data is 5c)
	bcs  L1617	    ; branch if lower
	addb #0x06	    ;  -00000110-
	ldaa MTHRMX_ValueOf_MINTHR_WhenBatteryDisconnected    ; load a with memory contents (data is 5c)
	cba		
	bcs  L1617	    ; branch if lower
	tba		    ; a = b
L1617:	staa MINTHR_LowestSessionTPS	; store a into memory
	ldaa PIA2_PortB_DataDirection	 ; load a with memory contents
	bita #0x08	    ;  -00001000-
	bne  L1618	    ; branch if not equal (not zero)
	brset *BitFlags_2e, #b2e_bit3, L1618	; branch if bit(s) set
	ldaa #0x09	    ; load a with value -00001001-
	staa CountdownTimerFromKeyOn	; store a into memory
	jmp  Setup11msLoop	    ; branch
L1618: 	anda #0xbf	    ; AND a with value -10111111-
	staa PIA2_PortB_DataDirection

Setup11msLoop:
	ldd  CPU_TimerCounterRegHigh
	addd #0x0005    ;  -00000000 00000101-
	std  CPU_Timer_OC1
	addd #0x0abb	    ;  add 11ms to the timer (11000us) after the 4x below
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	staa MinimumTimerCountBeforeMainloopCanContinue    ; store a into memory
	cli		    ; enable interrupts

MainProgramLoop:
	jsr  DealWithConfigurationAndPulseAccumulator_MM    ; call subroutine
MainLoop_ResetCOPTimer:
	cli		    ; enable interrupts
	ldd  #0x55aa	    ; reset the COP timer
	staa CPU_ArmResetCopTimerReg
	stab CPU_ArmResetCopTimerReg
	sei		    ; disable interrupts
	ldaa CPU_A2DControlReg	  ; load a with memory contents
	bpl  MainLoop_ResetCOPTimer	    ; branch if plus (hi bit 0)
	ldaa Counter_MainLoop	  ; load a with memory contents
	bita #0x03	    ;  -00000011-
	bne  L1621	    ; branch if not equal (not zero)
	ldaa CPU_A2DResults2	; load a with memory contents
	staa BatteryVolts    ; store a into memory
L1621:	ldd  CPU_A2DResults3
	cli		    ; enable interrupts
	staa RawAirFuelSensInput    ; store a into memory
	stab TPSVolts_11msUpdate    ; store b into memory
	jsr  ConvertWB2NBSignal_MM
	sei		    ; disable interrupts
	ldd  CPU_TimerCounterRegHigh
	stD *Temp0	    ; store D to RAM
	ldaa #0x14	    ; load a with value -00010100-
	staa CPU_A2DControlReg
	ldd  Temp0	    ; load d (a&b) with memory contents
	jsr  DetermineNumberOfOverflowsBetweenDistributorPulses_MM    ; call subroutine
	ldd  Temp0	    ; load d (a&b) with memory contents
	jsr  DetermineNumberOfOverflowsBetweenSpeedoPulses_MM	 ; call subroutine
L1622:	ldaa CPU_A2DControlReg	  ; load a with memory contents
	bpl  L1622	    ; branch if plus (hi bit 0)
	ldd  CPU_A2DResults1
	stD *RawCoolantTempVolts    ; B goes into 'RawChargeTempVolts'
	ldaa CPU_A2DResults4	; load a with memory contents
	staa AmbientAirTempVolts    ; store a into memory
	ldaa #0x10	    ; load a with value -00010000-
	staa CPU_A2DControlReg
	cli		    ; enable interrupts
	; jsr  EmmissionMaintenanceRemider1_MM	; call subroutine
	; jsr  EmmissionMaintenanceRemider2_MM ;RestoreSavedConfiguration2_MM    ; call subroutine
	jsr  CycleACClutch_MM    ; call subroutine
	jsr  DetermineIfWindowedBladeInSyncSensorOnDistributor_MM    ; call subroutine
	jsr  CheckThrottleRoutine_MM	; call subroutine
	jsr  CheckAndFilterCoolantAndChargeTempSensors_MM    ; call subroutine
	jsr  HandleBaroReadRequirement_MM    ; call subroutine
	jsr  CalculateInjectorPulsewidthForStarting_MM	  ; call subroutine
	jsr  DetectParkNeutral_MM    ; call subroutine
	jsr  CALCULATE_RPM_SPEED_AND	; call subroutine
	jsr  ControlAsdRelay_MM    ; call subroutine
	jsr  CalculateSparkAdvance_MM	 ; call subroutine
	jsr  ControlCruiseServo0_MM    ; call subroutine
	jsr  ControlCruiseServo1_MM    ; call subroutine
	; jsr  PrepareCCDDataForXmit_MM	  ; call subroutine
	jsr  KickUpAisBy2DuringDecel_MM    ; call subroutine
	jsr  CalculateTargetIdleSpeedAndAisPosition_MM	  ; call subroutine
	jsr  CalculateAisPosition_MM	; call subroutine
	jsr  CalculatePartThrottleEnrichmentAndSparkScatterFuel_MM    ; call subroutine
	jsr  HandleAmTimer_MM	 ; call subroutine
	jsr  HandleO2Processing_MM    ; call subroutine
	jsr  ModifyO2FeedbackCountVarToMaintainStoich_MM    ; call subroutine
	jsr  AdaptiveMemory_DetermineWhichCellApplies_MM    ; call subroutine
	jsr  AdaptiveMemory_UpdateCellIfRequired_MM    ; call subroutine
	jsr  DealWithSpecialIdle_SetBasicTiming_MM    ; call subroutine
	jsr  ControlEngineCutout_MM    ; call subroutine
	jsr  LaunchControl_MM
	jsr  CalculatePartThrottleTransientFuel_MM    ; call subroutine
	jsr  CalculateSumOfAllFuelModifiers_MM	  ; call subroutine
	jsr  ControlPurgeSolenoid_MM	; call subroutine
	jsr  ControlFan_MM    ; call subroutine
	jsr  ControlAirConditioning_MM	  ; call subroutine
	jsr  CalculateKnockRetard_MM	  ; call subroutine
        jsr  ControlPTU_MM
	jsr  UseCELForKnockIndication_MM     ; call subroutine
;        jsr  ControlShiftLight_MM
        jsr  CalculateNO2Retard_Routine_MM
	jsr  CalcTargetBoost_MM 	  ; lookup target boost
	jsr  CalcWGDutyCycle_MM           ; calculate WG duty cycle - this is modified from stock...
	jsr  GetControlFeedback_DetermineIfShutdownRequired_MM	  ; call subroutine
	jsr  VerifyOperationOfBatteryVoltage_MM    ; call subroutine
	jsr  DetectAlternatorFault_MM	 ; call subroutine
	jsr  CheckForErrorsAndSetCodes_MM    ; call subroutine
	jsr  VerifyOperationOfASDRelayAndO2Sensor_MM	; call subroutine
	jsr  VerifyOperationOfIgnitionCoilDriver_MM	; call subroutine
	jsr  VerifyOperationOfFuelInjectorDrivers_MM	; call subroutine
	jsr  VerifyOperationOfIgnitionCoilDriver2_MM    ; call subroutine
	jsr  VerifyOperationOfMapSensor_MM    ; call subroutine
	jsr  VerifyOperationOfThermostat_MM    ; call subroutine
	ldaa PIA2_PortB_DataDirection	 ; load a with memory contents
	bita #pia2b_bit6	    ;  -01000000-
	bne  L1623	    ; branch if not equal (not zero)
	sei		    ; disable interrupts
	ldd  #0xaaa5	    ; load d (a&b) with value -10101010 10100101-
	stD *L0000	    ; store D to RAM
	cli		    ; enable interrupts
L1623:	jsr  DetermineTargetBatteryVoltage_MM	 ; call subroutine
	jsr  ExhGasRecirc_MM	 ; call subroutine
	jsr  ThrowMajorErrorIfRequired_MM    ; call subroutine
	jsr  ProcessErrorBits_WorkWithData_MM    ; call subroutine
	jsr  UpdateErrorTimersAndPossiblyClearErrors_MM    ; call subroutine
	jsr  CheckIfCheckEngineLightShouldBeOn_MM    ; call subroutine
	jsr  DRBIISerialCommunications_MM    ; call subroutine
	jsr  DRBIIOuput_MM    ; call subroutine
	jsr  ActuatorTestMode_MM    ; call subroutine
	jsr  DRB_UpdatePIA1AndCheckOuputs_MM	; call subroutine
	jsr  IncrementLoopCounters_MM	 ; call subroutine
	ldaa MinimumTimerCountBeforeMainloopCanContinue    ; load a with memory contents
	staa Temp0	    ; store a into memory
	sei		    ; disable interrupts
	ldd  CPU_TimerCounterRegHigh
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	cmpa Temp0	    ; compare a with memory contents
	cli		    ; enable interrupts
	bpl  L1624	    ; branch if plus (hi bit 0)
	ldaa Temp0	    ; load a with memory contents
L1624:	adda #0x2b	    ; 11ms - 0x2b = 43d/4 = 10.75mSec
	staa MinimumTimerCountBeforeMainloopCanContinue    ; store a into memory
L1625:	ldd  CPU_TimerCounterRegHigh
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	cmpa Temp0	    ; compare a with memory contents
	bmi  L1625	    ; branch if minus(hi bit 1)
	jmp  MainProgramLoop

CheckAndFilterCoolantAndChargeTempSensors_MM:
	brclr *Counter_MainLoop, #$%00000111, L2626	; branch if bit(s) clear  ** this loop only runs every ~80ms **
	rts		                  ; return from subroutine

L2626:	ldaa CONFIG_ConfigurationFlags	  ; load a with memory contents (data is 02)
	bita #cfg_CTS		          ;  -10000000-
	bne  FilterAndStoreChargeTemp	  ; branch if bit is set
        ldab 0x00                         ;set to 0 to force 0 return for charge temp lookups...
        stab ChargeTemp
        bra  CheckCoolantTempSensor

FilterAndStoreChargeTemp:
	ldab #0x1c	                  ; load b with value -00011100-
	ldaa RawChargeTempVolts           ; load a with memory contents
	cmpa CHGLOW_ChargeTempOutOfRangeLow    ; compare a with memory contents (data is 08)
	bcs  SetChargeTempError	          ; branch if lower
	incb
	cmpa CHGHIG_ChargeTempOutOfRangeHigh	; compare a with memory contents (data is fd)
	bhi  SetChargeTempError	          ; branch if higher
	brclr *b45_IPL1, #b45_BadChargeTemp, FilterChargeTemp	 ; branch if bit(s) clear
	ldaa #0x01	                  ; load a with value -00000001-
	jsr  ResetErrorCodeIfTimerExpired ; call subroutine
	bra  UseLimpinForChargeTemp       ; branch

FilterChargeTemp:
	ldab ChargeTemp	; load b with memory contents
	sba		    ; subtract (a=a-b)
	bcc  L1626	    ; branch if greater or equal
	decb
	bra  StoreChargeTemp	    ; branch

L1626:	cmpa #0x03	    ; compare a with value -00000011-
	bcs  CheckCoolantTempSensor	    ; branch if lower
	incb
	bra  StoreChargeTemp	    ; branch

UseLimpinForChargeTemp:
	ldab DEFCHG_DefaultChargeTemp_Limpin	; load b with memory contents (data is ad)
StoreChargeTemp:
	stab ChargeTemp	; store b into memory
	bra  CheckCoolantTempSensor	    ; branch

SetChargeTempError:
	brset *b45_IPL1, #b45_BadChargeTemp, UseLimpinForChargeTemp	; branch if bit(s) set
	tba		    ; a = b
	ldab #0x94	    ; load b with value -10010100-
	jsr  ThrowNonCriticalError    ; call subroutine
	bcc  CheckCoolantTempSensor	    ; branch if greater or equal
	bset *b45_IPL1, #b45_BadChargeTemp    ; set bits

CheckCoolantTempSensor:
        ldab #0x1f	    ; load b with value -00011111-
	ldaa RawCoolantTempVolts    ; load a with memory contents
	cmpa TMPHIG_OutOfRangeColdTooHighA2D    ; compare a with memory contents (data is fd)
	bcc  SetCoolantTempError	    ; branch if greater or equal
	decb
	cmpa TMPLOW_OutOfRangeHotTooLowA2D	; compare a with memory contents (data is 1a)
	bcs  SetCoolantTempError	    ; branch if lower
	brclr *b45_IPL1, #b45_BadCoolantTemp, DetermineWhichCoolantTempScaleToUse	; branch if bit(s) clear
	ldaa #0x02	    ; load a with value -00000010-
	jsr  ResetErrorCodeIfTimerExpired    ; call subroutine
	bra  SubstituteChargeTempForCoolantTemp    ; branch

DetermineWhichCoolantTempScaleToUse:
	ldx  #TMPTL2_TempForHotScaleA2D    ; load index with value
	ldab PIA2_PortB_DataDirection	 ; load b with memory contents
	bpl  L1632	    ; branch if plus (hi bit 0)
	ldx  #TMPTL1_TempForColdScaleFromA2D	; load index with value
	cmpa #0x40	    ; compare a with value -01000000-
	bcc  FilterAndStoreCoolantTemp	  ; branch if greater or equal
ToggleCoolantTempScale:
	brset *BitFlags_2e, #b2e_bit7 | b2e_bit6, L1630    ; branch if bit(s) set
	ldab BitFlags_2e    ; load b with memory contents
	addb #b2e_bit6		;  -01000000-
	stab BitFlags_2e    ; store b into memory
	bra  L1633	    ; branch

L1630:	bclr *BitFlags_2e, #b2e_bit7 | b2e_bit6    ; clear bits
	ldab #0x80	    ; load b with value -10000000-
	sei		    ; disable interrupts
	eorb PIA2_PortB_DataDirection
	stab PIA2_PortB_DataDirection	 ; store b into memory
	cli		    ; enable interrupts
R1631:	rts		    ; return from subroutine

L1632:	cmpa #0xdc	    ; compare a with value -11011100-
	bcc  ToggleCoolantTempScale    ; branch if greater or equal
FilterAndStoreCoolantTemp:
	bclr *BitFlags_2e, #b2e_bit7 | b2e_bit6    ; clear bits
L1633:	jsr  Lookup4ByteTable	 ; call subroutine
	ldab CoolantTemp    ; load b with memory contents
	sba		    ; subtract (a=a-b)
	bcc  L1634	    ; branch if greater or equal
	decb		
	bra  StoreCoolantTemp	    ; branch

L1634:	cmpa #0x03	    ; compare a with value -00000011-
	bcs  R1631	    ; branch if lower
	incb		
	bra  StoreCoolantTemp	    ; branch

SubstituteChargeTempForCoolantTemp:
	ldab DEFTMP_DefaultEngineTemp	 ; load b with memory contents (data is 95)
	brset *b45_IPL1, #b45_BadChargeTemp, StoreCoolantTemp    ; branch if bit(s) set

	ldaa CONFIG_ConfigurationFlags
	bita #cfg_CTS		          
	beq  StoreCoolantTemp	                  ; branch if bit is not set

	ldaa RawChargeTempVolts    ; load a with memory contents
	ldx  #CHGTL1_TempForChargeTempA2D    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine

StoreCoolantTemp:
	stab CoolantTemp    ; store b into memory
	rts		    ; return from subroutine

SetCoolantTempError:
	brset *b45_IPL1, #b45_BadCoolantTemp, SubstituteChargeTempForCoolantTemp    ; branch if bit(s) set
	tba		    ; a = b
	ldab #0x9e	    ; load b with value -10011110-
	jsr  ThrowNonCriticalError    ; call subroutine
	bcc  R1631	    ; branch if greater or equal
	ldaa #0x7f	    ; load a with value -01111111-
	sei		    ; disable interrupts
	anda PIA2_PortB_DataDirection
	staa PIA2_PortB_DataDirection
	cli		    ; enable interrupts
	bset *b45_IPL1, #b45_BadCoolantTemp	  ; set bits
	bclr *BitFlags_4f, #b4f_O2Valid    ; clear bits
	clra		    ; a = 0
	staa Timer_CLTIME_ClosedLoopTimer    ; store a into memory
	staa Timer_ThermostatDiagnostics    ; store a into memory
	rts		    ; return from subroutine

DetermineIfWindowedBladeInSyncSensorOnDistributor_MM:
	ldaa BitFlags_51                                   ; load a with memory contents
	brclr *BitFlags_54, #b54_FuelEngineNotRunning, ResetINSYC3Flag	; branch if bit(s) clear
	brset *BitFlags_55, #b55_SearchBladeEndRef_INSYNC, ResetINSYC3Flag    ; branch if bit(s) set
	ldab CPU_PortA		                           ; load b with memory contents
	bitb #CPU_PortA_DistRef	                           ;	-00000100-
	bne  ResetSYCLOWFlag	                           ; branch if not equal (not zero)
	ldab SwitchPortAccessReg                           ; load b with memory contents
	bitb #swp_DistSync	                           ;  -00100000-
	bne  CheckConditionOfSYCLOWFlag	                   ; branch if not equal (not zero)
SetSYCLOWFlag:
	oraa #b51_EndOfBlade_SYCLOW	                   ;  -00000001-
	bra  StoreSyncFlags	                           ; branch

CheckConditionOfSYCLOWFlag:
	bita #b51_EndOfBlade_SYCLOW	                   ;  -00000001-
	beq  EndSync	                                   ; branch if equal (zero)
SetINSYC3Flag:
	oraa #b51_BladePassedSensor_INSYC3	           ;  -00000010-
	bra  StoreSyncFlags	                           ; branch
ResetINSYC3Flag:
	anda #~b51_BladePassedSensor_INSYC3	           ; AND a with value -11111101-
ResetSYCLOWFlag:
	anda #~b51_EndOfBlade_SYCLOW	                   ; AND a with value -11111110-
StoreSyncFlags:
	staa BitFlags_51                                   ; store a into memory
EndSync:
	rts		    

CheckThrottleRoutine_MM:
	ldab #0x1a	    ; load b with value -00011010-
	ldaa TPSVolts_11msUpdate    ; load a with memory contents
	cmpa THRLOW_ThrottleLowerLimit	  ; compare a with memory contents (data is 08)
	bcs  CheckThrottle_BadTpsSignal    ; branch if lower
	incb
	cmpa THRHIG_ThrottleUpperLimit	  ; compare a with memory contents (data is f0)
	bcc  CheckThrottle_BadTpsSignal    ; branch if greater or equal
	brclr *b45_IPL1, #b45_TpsBadSignal, CheckThrottle_GotTpsValue    ; branch if bit(s) clear
	ldaa #0x07	    ; load a with value -00000111-
	bita Counter_MainLoop
	bne  CheckThrottle_ErrorAlreadyFlagged	  ; branch if not equal (not zero)
	jsr  ResetErrorCodeIfTimerExpired    ; call subroutine
	bra  CheckThrottle_ErrorAlreadyFlagged	  ; branch

CheckThrottle_BadTpsSignal:
	brset *b45_IPL1, #b45_TpsBadSignal, CheckThrottle_ErrorAlreadyFlagged    ; branch if bit(s) set
	brclr *Counter_MainLoop, #$%00000001, L1644	; branch if bit(s) clear
	tba		    ; a = b
	ldab #0xa0	    ; load b with value -10100000-
	jsr  ThrowNonCriticalError    ; call subroutine
	bcc  L1644	    ; branch if greater or equal
	bset *b45_IPL1, #b45_TpsBadSignal	; set bits
CheckThrottle_ErrorAlreadyFlagged:
	ldaa #0x40	    ; load a with value -01000000-
	staa MINTHR_LowestSessionTPS	; store a into memory
	brset *BitFlags_54, #b54_FuelEngineNotRunning, CheckThrottle_GotTpsValue    ; branch if bit(s) set
	ldab MapValue	    ; load b with memory contents
	cmpb MPTHR_MapSwitchPointForFullThrottleOrIdle	  ; compare b with memory contents (data is 45)
	bcs  CheckThrottle_GotTpsValue	  ; branch if lower
	adda WOTDLT_DeltaThrottleFrom_MINTHR_ToDetermineFullThrottle	;  (data is 85)
CheckThrottle_GotTpsValue:
	staa TpsVolts	    ; store a into memory

; here, check if launch control is active and force WOT flag if it is...
	brset *Turbonator_Flags, #Turbonator_Staging, CheckThrottle_AtFullThrottle

	ldab WOTDLT_DeltaThrottleFrom_MINTHR_ToDetermineFullThrottle	; load b with memory contents (data is 85)
	addb MINTHR_LowestSessionTPS	; b=b+memory contents
	cmpb #0xd0	    ;  -11010000-
	bls  L1642	    ; branch if lower or same
	ldab #0xd0	    ; load b with value -11010000-
L1642:	brclr *BitFlags_4f, #b4f_FullThrottle, L1643	; branch if bit(s) clear
	subb #0x03	    ;  -00000011-
L1643:	cba
	bhi  CheckThrottle_AtFullThrottle    ; branch if higher
	bclr *BitFlags_4f, #b4f_FullThrottle	; clear bits
	bra  L1644	    ; branch

CheckThrottle_AtFullThrottle:
	bset *BitFlags_4f, #b4f_FullThrottle	; set bits
L1644:	ldaa TpsVolts	    ; load a with memory contents
	ldab BitFlags_4f    ; load b with memory contents
	bmi  L1646	    ; branch if minus(hi bit 1) - b4f_OffIdle
	cmpa MINTHR_LowestSessionTPS	; compare a with memory contents
	bcc  L1646	    ; branch if greater or equal
	ldaa Timer_CountdownFromStartRunForAisFeedback	  ; load a with memory contents
	bne  L1646	    ; branch if not equal (not zero)
	brset *BitFlags_54, #b54_FuelEngineNotRunning, L1646	; branch if bit(s) set
	brclr *KeyOnOrEngineRunningTime, #$%11111111, L1646    ; branch if bit(s) clear
	ldaa Timer_DelayBeforeUpdating_MINTHR	 ; load a with memory contents
	deca		    ; decrement a
	bne  L1647	    ; branch if not equal (not zero)
	ldaa MINTHR_LowestSessionTPS	; load a with memory contents
	deca		    ; decrement a
	bge  L1645	    ; branch if greater or equal
	ldaa MTHRMX_ValueOf_MINTHR_WhenBatteryDisconnected    ; load a with memory contents (data is 5c)
L1645:	staa MINTHR_LowestSessionTPS	; store a into memory
	andb #~b4f_UpdatedMINTHR	    ;  -10111111-
L1646:	ldaa MAXCNT_ProgramLoopsWithThrottleBelow_MINTHR_ToDecrement_MINTHR    ; load a with memory contents (data is 10)
L1647:	staa Timer_DelayBeforeUpdating_MINTHR	 ; store a into memory
	ldaa MTHRCL_NumberOfBitsAbove_MINTHR_ToDetermineOnThrottleTransition	; load a with memory contents (data is 02)
	tstb
	bpl  L1648	    ; branch if plus (hi bit 0)
	ldaa MTHROP_NumberOfBitsAbove_MINTHR_ToDetermineOffThrottleTransition	 ; load a with memory contents (data is 01)
L1648:	adda MINTHR_LowestSessionTPS
	cmpa TpsVolts	    ; compare a with memory contents
	bcc  CheckThrottle_AtIdle    ; branch if greater or equal
	tstb		
	bmi  L1654	    ; branch if minus(hi bit 1)
	bitb #b4f_UpdatedMINTHR	    ;  -01000000-
	bne  L1649	    ; branch if not equal (not zero)
	ldaa MINTHR_LowestSessionTPS	; load a with memory contents
	inca		    ; increment a
	cmpa TpsVolts	    ; compare a with memory contents
	bcc  L1649	    ; branch if greater or equal
	staa MINTHR_LowestSessionTPS	; store a into memory
	orab #b4f_UpdatedMINTHR	    ;  -01000000-
L1649:	ldaa MapValue	    ; load a with memory contents
	suba OCTAE_FakeDeltaMapIncrease    ;  (data is 01)
	bcc  L1650	    ; branch if greater or equal
        ldaa MINAMP_MinimumAverageMAP
L1650:	staa AverageMAPValue    ; store a into memory
	ldaa TpsVolts	    ; load a with memory contents
	staa AverageTPSVolts    ; store a into memory
	orab #b4f_OffIdle	    ;  -10000000-
	bra  L1654	    ; branch

CheckThrottle_AtIdle:
	tstb		
	bpl  L1654	    ; branch if plus (hi bit 0)
	brset *BitFlags_AIS, #b0c_bit4, L1651	 ; branch if bit(s) set
	bset *BitFlags_2e, #b2e_AtIdle	  ; set bits
L1651:	ldx  #DLYTIM_AisDelayAfterThrottleClosesWhenMoving	    ; load index with value
	stab Temp0	    ; store b into memory
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	cmpa MPHREF_SwitchPointForDecelIdleAisControl	 ; compare a with memory contents (data is 07)
	bhi  CheckThrottle_VehicleSpeedStillAboveDecelIdle    ; branch if higher
	inx		    ; increment index (x=x+1)
	ldaa DLYTM3_AisDelayAfterThrottleClosesWhenRpmAbove_DLYRPM    ; load a with memory contents (data is ff)
	ldab EngineRpm_HB    ; load b with memory contents
	cmpb DLYRPM_RpmTriggerForAisDelay    ; compare b with memory contents (data is da)
	bcc  L1652	    ; branch if greater or equal
CheckThrottle_VehicleSpeedStillAboveDecelIdle:
	ldaa 0x00,x	    ; load a with memory at index + value
L1652:	cmpa Timer_CountdownFromStartRunForAisFeedback	  ; compare a with memory contents
	bls  L1653	    ; branch if lower or same
	staa Timer_CountdownFromStartRunForAisFeedback	  ; store a into memory
L1653:	ldab Temp0	    ; load b with memory contents
	andb #~b4f_OffIdle	    ;  -01111111-
L1654:	bitb #b4f_PartThrottle	    ;  -00001000-
	bne  L1656	    ; branch if not equal (not zero)
	brclr *StartupSwitchMirror2, #sw2_Brake, L1656    ; branch if bit(s) clear
	ldaa EngineRpm_HB    ; load a with memory contents
	cmpa RPMTHR_ThrottleSelfCalibrationRpmThreshold    ; compare a with memory contents (data is 30)
	bcs  L1656	    ; branch if lower
	ldaa MapValue	    ; load a with memory contents
	cmpa MAPTHR_ThrottleSelfCalibrationMapDeltaThreshold	; compare a with memory contents (data is 20)
	bcc  L1656	    ; branch if greater or equal
	ldaa MINTHR_LowestSessionTPS	; load a with memory contents
	inca		    ; increment a
	cmpa MTHRMX_ValueOf_MINTHR_WhenBatteryDisconnected    ; compare a with memory contents (data is 5c)
	bcs  L1655	    ; branch if lower
	ldaa MTHRMX_ValueOf_MINTHR_WhenBatteryDisconnected    ; load a with memory contents (data is 5c)
L1655:	staa MINTHR_LowestSessionTPS	; store a into memory
	orab #b4f_PartThrottle	    ;  -00001000-
L1656:	ldaa MINTHR_LowestSessionTPS	; load a with memory contents
	adda #0x30	    ;  -00110000-
	cmpa TpsVolts	    ; compare a with memory contents
	bcc  L1657	    ; branch if greater or equal
	andb #~b4f_PartThrottle 	 ;  -11110111-
L1657:	stab BitFlags_4f    ; store b into memory
	rts		    ; return from subroutine

ConvertMAPVoltsToValue:
	staa Temp5	    ; store a into memory
	ldab MAPMULT_ScaleMAPVoltsToPresMultiplyConst
	bpl  L1658	    ; branch if plus (hi bit 0)
	clr  Temp5	    ; zero byte at memory location
L1658:	mul		    ; multiply (d=a*b)
	adda Temp5	
	bcc  L1659	    ; branch if greater or equal
	ldaa #0xff	    ; load a with value -11111111-
L1659:	addd MAPADD_ScaleMAPVoltsToPresAddConst
	bcc  L1660	    ; branch if greater or equal
	ldaa #0xff	    ; load a with value -11111111-
L1660:	rts		    ; return from subroutine

CalculateSparkAdvance_MM:
;  Dwell calculation:
;
;  The dwell lookup/calculation is pretty simple.
;
;  First, the ideal dwell period is calculated from the complement of the 
;  lookup value from battery volts. Battery volts is the largest factor for
;  determining dwell period. The complement is used because the 16-bit 
;  table type cannot have a negative slope.
;
;  Then, the Ditributor PW is compared to the ideal dwell period plus the
;  the minimum antidwell period. If the dwell + min anti dwell is greater 
;  than the distributor PW, then the minimum antidwell is used. Otherwise,
;  the ideal dwell is used and the anit-dwell is set to the difference
;  between the distributor PW and the dwell (floating anti-dwell).
;
;  Logically --> If (DWELL + MINADW) < DISTPW 
;                   Then ADWELL = DISTPW - DWELL
;                   Else ADWELL = MINADW

        ldaa  BatteryVolts    ; load A with memory contents
        ldx   #DWELL_DwellTimeFromBatteryVoltsComp    ; load index with value
        jsr   Lookup5ByteTable    ; call subroutine
        coma                ; 1's complement A
        comb                ; 1's complement B
        std   DwellTime_HB

	clra		    ; a = 0
	staa Temp0	    ; store a into memory
	ldab CoolantTemp    ; load b with memory contents
	cmpb TMPSWP_EngTempSwitchPointForSparkAdvance	 ; compare b with memory contents (data is 92)
	bcc  SparkAdvance_TempAboveTMPSWP    ; branch if greater or equal
	ldx  #CLDMAP_AdvanceFromMAPCold    ; load index with value
	jsr  SparkAdvance_GetAdvanceFromTableUsingMap	 ; call subroutine
	brset *BitFlags_4f, #b4f_OffIdle, L1666    ; branch if bit(s) set
	cmpa CLDLMT_LimitForColdMapAtClosedThrottle    ; compare a with memory contents (data is 28)
	blt  L1661	    ; branch if less
	ldaa CLDLMT_LimitForColdMapAtClosedThrottle    ; load a with memory contents (data is 28)
L1661:	staa Temp0	    ; store a into memory
SparkAdvance_NoThrottle:
	ldab EngineRpm_HB    ; load b with memory contents
	cmpb PNRPM_EngineSpeedBelowWhich_PNIDLE_Enabled    ; compare b with memory contents (data is 24)
	bhi  DetermineMechanicalAdvanceFromRpm	  ; branch if higher
	brset *BitFlags_AIS, #b0c_ATXInGear, DetermineMechanicalAdvanceFromRpm	  ; branch if bit(s) set
	ldaa CoolantTemp    ; load a with memory contents
	ldx  #PNIDLE_AdvanceRemovedIdleParkNeutral    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	adda Temp0	
	bra  L1666	    ; branch

SparkAdvance_TempAboveTMPSWP:
	brclr *BitFlags_4f, #b4f_OffIdle, SparkAdvance_NoThrottle    ; branch if bit(s) clear
	ldx  #WOTMAP_AdvanceFromMAPWarmFull    ; load index with value
DetermineHotAdvanceFromMap:
	jsr  SparkAdvance_GetAdvanceFromTableUsingMap	 ; call subroutine
	brset *BitFlags_4f, #b4f_FullThrottle, L1664	; branch if bit(s) set
	staa Temp0	    ; store WOT timing into A, for comparison later
	ldx  #HOTMAP_AdvanceFromMAPWarmPart    ; load index with value
	ldaa MapValue	    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Temp1	    ; store a into memory
	ldx  #ADVCLS_AdvanceAddedForClosedLoopFromTimer    ; load index with value
	ldaa Timer_OpenLoopFraction    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	adda Temp1	    ; add advance from open loop to P/T timing
	bvc  L1663	    ; branch if overflow - only happen when advance from MAP is negative (high boost)
	tsta		    ; test a
	bpl  L1662	    ; branch if plus (hi bit 0)
	ldaa #0x7f	    ; load a with value -01111111- (Maximum, plus)
	bra  L1663	    ; branch

L1662:	ldaa #0x80	    ; load a with value -10000000- (negative 0)
L1663:	bsr  IncludeAdaptiveRetard	    ; call subroutine
	cmpa Temp0	    ; compare WOT timing
	bge  L1665	    ; branch if greater or equal

L1664:	suba NO2Retard ; maybe I should include the anit-lag retard here instead. It will be more like the 87 code, then

        staa Temp0	    ; store a into memory
L1665:	ldx  #RPMLMT_LimitForHotMAPAdvance    ; load index with value
	ldaa EngineRpm_HB    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	cmpa Temp0	    ; compare a with memory contents
	bgt  DetermineMechanicalAdvanceFromRpm	  ; branch if A is greater Temp0
L1666:	staa Temp0	    ; store a into memory
DetermineMechanicalAdvanceFromRpm:
	ldx  #GOVNER_AdvanceFromRPM    ; load index with value
	ldaa EngineRpm_HB    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	ldab MapValue	    ; load b with memory contents
	cmpb ARMPIC_AdaptiveRetard_MinMAPForAdjustment	  ; compare b with memory contents (data is 50)
	bls  L1667	    ; branch if lower or same
	staa Temp1	    ; store a into memory
	ldx  #ARRPM_AdaptiveRetardFromRPM    ; load index with value
	ldaa EngineRpm_HB    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	ldab AdaptiveRetardIndex    ; load b with memory contents
	mul		    ; multiply (d=a*b)
	adca #0x00	    ;  -00000000-
	tab		    ; b = a
	ldaa Temp1	    ; load a with memory contents
	sba		    ; subtract (a=a-b)
	bcc  L1667	    ; branch if greater or equal
	clra		    ; a = 0
L1667:	cmpa ADVDFT_DefaultSparkAdvance1    ; compare a with memory contents (data is 14)
	bcc  L1668	    ; branch if greater or equal
	brset *BitFlags_4f, #b4f_OffIdle, L1668    ; branch if bit(s) set
	ldaa ADVDFT_DefaultSparkAdvance1    ; load a with memory contents (data is 14)
L1668:	adda Temp0
        bpl  CheckMaxSparkAdvance
	clra		             ; a = 0
CheckMaxSparkAdvance:
	staa Temp0	    ; store a into memory
	ldx  #SPKLMT_TotalAdvanceAllowed    ; load index with value
	ldaa EngineRpm_HB    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	cmpa Temp0	    ; compare a with memory contents
	bcs  L1669	    ; branch if lower
	ldaa Temp0	    ; load a with memory contents
L1669:	ldab BitFlags_54    ; if engine is off-idle or is not running (?)
	orab BitFlags_4f
	bmi  STORE_SPARK_ADV	; branch if minus(hi bit 1)  - off-idle
	ldab BitFlags_AIS    ; load b with memory contents
	andb #b0c_ATXChngGear	       ;  -00000100-
	orab Timer_CountdownFromStartRunForAisFeedback
	bne  STORE_SPARK_ADV	; branch if not equal (not zero)
	brset *BitFlags_50, #b50_FallToIdle, STORE_SPARK_ADV	; branch if bit(s) set
	brclr *b45_IPL1, #b45_BadCoolantTemp, STORE_SPARK_ADV    ; branch if bit(s) clear
	ldaa SPKSET_ConstantSparkAdvanceWhenSettingBasicTiming    ; load a with memory contents (data is 0c)
STORE_SPARK_ADV:
	staa CalculatedSparkAdvance    ; store a into memory
	rts		    ; return from subroutine

SparkAdvance_GetAdvanceFromTableUsingMap:
	ldaa MapValue	    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
IncludeAdaptiveRetard:
	ldab MapValue	    ; load b with memory contents
	cmpb ARMPIC_AdaptiveRetard_MinMAPForAdjustment	  ; compare b with memory contents (data is 50)
	bls  IncludeMAPAdvMultiplier	    ; branch if lower or same
	staa Temp1	    ; store a into memory
	ldaa MapValue	    ; load a with memory contents
	ldx  #ARMAP_AdaptiveRetardFromMAP    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	ldab AdaptiveRetardIndex    ; load b with memory contents
	mul		    ; multiply (d=a*b)
	adca #0x00	    ;  -00000000-
	tab		    ; b = a
	ldaa Temp1	    ; load a with memory contents
	sba		    ; subtract (a=a-b)
	bvc  IncludeMAPAdvMultiplier	    ; branch if overflow
	ldaa #0x80	    ; load a with value -10000000-
IncludeMAPAdvMultiplier:
	tsta		    ; test a
	bpl  L1674	    ; branch if plus (hi bit 0)
	nega		    ; negate a (2's compl)
	staa Temp1	    ; store a into memory
	ldaa EngineRpm_HB    ; load a with memory contents
	ldx  #MAPMUL_MultiplierOnMapAdvanceWhenRetarding_FromRpm    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	ldaa Temp1	    ; load a with memory contents
	mul		    ; multiply (d=a*b)
	asld		    ; shift left (d=d*2)
	bmi  L1672	    ; branch if minus(hi bit 1)
	asld		    ; shift left (d=d*2)
	bmi  L1672	    ; branch if minus(hi bit 1)
	tstb		
	bpl  L1673	    ; branch if plus (hi bit 0)
	inca		    ; increment a
	bpl  L1673	    ; branch if plus (hi bit 0)
L1672:	ldaa #0x81	    ; load a with value -10000001-
	rts		    ; return from subroutine

L1673:	nega		    ; negate a (2's compl)
L1674:	rts		    ; return from subroutine

HandleSparkScatter:
	ldaa BitFlags_54    ; load a with memory contents
	oraa BitFlags_4f    ; OR a with memory contents
	bmi  R1675	    ; branch if minus(hi bit 1) - branch if off-idle or engine not running
	ldaa BitFlags_AIS    ; load a with memory contents
	anda #b0c_ATXChngGear	       ; AND a with value -00000100-
	oraa Timer_CountdownFromStartRunForAisFeedback	  ; OR a with memory contents
	bne  R1675	    ; branch if not equal (not zero)
	brset *BitFlags_50, #b50_FallToIdle, R1675    ; branch if bit(s) set
	brclr *b45_IPL1, #b45_BadCoolantTemp, L1676	  ; branch if bit(s) clear
R1675:	rts		    ; return from subroutine

L1676:	brclr *b45_IPL1, #b45_MapStuck | b45_MapBadSignal, L1677    ; branch if bit(s) clear
	bra  DontUseSparkScatter    ; branch

L1677:	ldab CoolantTemp    ; load b with memory contents
	cmpb SSTEMP_TempAboveWhichSparkScatterIsActive	  ; compare b with memory contents (data is 58)
	bls  DontUseSparkScatter    ; branch if lower or same
	ldx  KeyOnOrEngineRunningTime
	cpx  SSITIM_ScatterInhibitTime	  ;  (data is 0088)
	bcs  DontUseSparkScatter    ; branch if lower
	ldx  TimerOverflowsBetweenDistPulses
	cpx  SSIPRD_ScatterInhibitBelowThisSpeed    ;  (data is 0033)
	bcc  DontUseSparkScatter    ; branch if greater or equal
	ldx  #SPKRET_SparkAdvanceRetardedWhenRpmAboveControl_FromDeltaRpm    ; load index with value
	ldd  EngineRpm_HB    ; load d (a&b) with memory contents
	subd TargetIdleSpeed_HB	; d = d - memory contents
	bcc  L1678	    ; branch if greater or equal
	ldx  #SPKADD_SparkAdvanceAddedWhenRpmBelowControl_FromDeltaRpm	  ; load index with value
	coma		
	comb		
	addd #0x0001	     ;	-00000000 00000001-
L1678:	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	bcc  L1679	    ; branch if greater or equal
	addd #0x0001	     ;	-00000000 00000001-
L1679:	tsta		    ; test a
	beq  L1680	    ; branch if equal (zero)
	ldab #0xff	    ; load b with value -11111111-
L1680:	tba		    ; a = b
	jsr  Lookup4ByteTable	 ; call subroutine
	addb CalculatedSparkAdvance    ; b=b+memory contents
	stab Temp5	    ; store b into memory
	bset *BitFlags_55, #b55_UseSparkScatter    ; set bits
	adda SparkScatter
	bvc  DoUseSparkScatter	  ; branch if overflow
	ldab DesiredNewAisPosition    ; load b with memory contents
	cmpb CurrentAisPosition
	bne  DontUseSparkScatter    ; branch if not equal (not zero)
	ldab FTUNPW_FineTuneStepForAis	  ; load b with memory contents (data is 01)
	beq  DontUseSparkScatter    ; branch if equal (zero)
	tsta		    ; test a
	bmi  L1681	    ; branch if minus(hi bit 1)
	ldaa DesiredNewAisPosition    ; load a with memory contents
	sba		    ; subtract (a=a-b)
	bcc  SaveDesiredAisPosition    ; branch if greater or equal
	clra		    ; a = 0
	bra  SaveDesiredAisPosition    ; branch

L1681:	ldaa AISHLM_AisHighLimitMaxOpenSteps	; load a with memory contents (data is a0)
	addb DesiredNewAisPosition    ; b=b+memory contents
	bcs  SaveDesiredAisPosition    ; branch if lower
	cba		
	bls  SaveDesiredAisPosition    ; branch if lower or same
	tba		    ; a = b
SaveDesiredAisPosition:
	staa DesiredNewAisPosition    ; store a into memory
DontUseSparkScatter:
	clra		    ; a = 0
DoUseSparkScatter:
	staa SparkScatter    ; store a into memory
	ldaa DRBPointer1    ; load a with memory contents
	cmpa #0x14	    ; compare a with value -00010100-
	bne  R1682	    ; branch if not equal (not zero)
	ldaa DRBPointer2    ; load a with memory contents
	cmpa #0x10	    ; compare a with value -00010000-
	bne  R1682	    ; branch if not equal (not zero)
	ldab IDLSET_ConstantSparkAdvanceWhenSettingMinThrottleOpening	 ; load b with memory contents (data is 0c)
	stab Temp5	    ; store b into memory
	bclr *BitFlags_55, #b55_UseSparkScatter    ; clear bits
R1682:	rts		    ; return from subroutine

InterruptVector_DwellTimer:
; this routine sets up the rising/falling edge detection for the distributor and also loads the dwell timer with 
; the approriate value depending on rising/falling edge of the shutter

	ldaa #CPU_TIFlag1_OC5Dwell	    ; clear the dwell flag
	staa CPU_TimerInterruptFlag1
	ldaa TimerOverflowsBetweenDistPulses	; load a with memory contents
	bne  R1683	    ; branch if not equal (not zero)
	brset *BitFlags_54, #b54_DisableNormalDwell, R1683    ; branch if bit(s) set
	brclr *BitFlags_55, #b55_SearchBladeEndRef_INSYNC, R1683    ; branch if bit(s) clear

NormalDwell:
	ldaa CPU_TimerControlReg1    ; load a with memory contents
	eora #0x01	             ; toggle the toggle bits for OC5 pin on successful compare
	staa CPU_TimerControlReg1
	lsra		             ; check if the toggle bits are set
	bcs  IgnitionCoil_OnTimeLoad ; branch if bit 1 is set - OC5 setup to set on compare
	ldd  CPU_TimerControlReg1
	bitb #0x10	             ;  check edge detection on IC1 (dist signal) for rising edge only
	bne  IgnitionCoil_OffTimeLoad	 ; branch if edge detection bit is set...
	oraa #0x01	             ;  set OC5 to set on successful compare
	staa CPU_TimerControlReg1
R1683:	rti		    ; return from interrupt

IgnitionCoil_OnTimeLoad:
	ldd  AntiDwellTime_HB	    ; load d (a&b) with memory contents
	bra  L1684	    ; branch

IgnitionCoil_OffTimeLoad:
	ldd  DistributorFallingEdgePulsewidth_HB    ; load d (a&b) with memory contents
	subd AntiDwellTime_HB	    ; d = d - memory contents
L1684:	addd CPU_Timer_OC5_Dwell
	std  CPU_Timer_OC5_Dwell
	rti		    ; return from interrupt

CalculateKnockRetard_MM:
	clra		    ; a = 0
	ldab EngineRpm_HB    ; load b with memory contents
	cmpb KNKRPM_MinRpmforKnockRetard    ; compare b with memory contents (data is 20)
	bcs  StoreMaxAllowedRetard    ; branch if lower
	deca		    ; decrement a
	ldab b45_IPL1    ; load b with memory contents
	andb #b45_MapStuck | b45_TpsBadSignal | b45_MapBadSignal	  ;  -11100000-
	bne  CalculateMaxAllowedRetard	  ; branch if not equal (not zero)
	ldaa MapValue	    ; load a with memory contents
	ldab TpsVolts	    ; load b with memory contents
	subb MINTHR_LowestSessionTPS	; b = b-memory contents
	bcs  CalculateMaxAllowedRetard	  ; branch if lower
	cmpb THRKNK_DeltaAbove_MINTHR	 ; compare b with memory contents (data is 53)
	bcs  CalculateMaxAllowedRetard	  ; branch if lower
	ldab EngineRpm_HB    ; load b with memory contents
	cmpb KLMRPM_MinKnockDetectRpm	 ; compare b with memory contents (data is 20)
	bcc  CalculateMaxAllowedRetard	  ; branch if greater or equal
	ldaa KNKLIM_MaxKnockRetard    ; load a with memory contents (data is 05)
	bra  StoreMaxAllowedRetard    ; branch

CalculateMaxAllowedRetard:
	ldx  #RETMAX_MaxKnockRetardFromMap    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
StoreMaxAllowedRetard:
	staa MaxRetardFromMAP	 ; store a into memory
	ldaa EngineRpm_HB    ; load a with memory contents
	ldx  #DLTKNK_KnockFromRpms    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	staa KnockSensorThreshold    ; store a into memory
	ldaa Counter_MainLoop	  ; load a with memory contents
	bita INCSRT_KnockRetardIncreaseRate    ;  (data is 1f)
	bne  R1686	    ; branch if not equal (not zero)
	ldx  #Cylinder2Retard	 ; load index with value
ReduceAllRetardsByOne:
	sei		    ; disable interrupts
	ldaa 0x00,x	    ; load a with memory at index + value
	beq  L1685	    ; branch if equal (zero)
	deca		    ; decrement a
	staa 0x00,x	
L1685:	cli		    ; enable interrupts
	inx		    ; increment index (x=x+1)
	cpx  #Cylinder4Retard	 ;  -00000000 10100100-
	bls  ReduceAllRetardsByOne    ; branch if lower or same
R1686:	rts		    ; return from subroutine

DetermineIfSpeedoSensorOnOrOff:
	ldaa CPU_TimerControlReg2    ; load a with memory contents
	lsra
	eora CPU_PortA	    
	bita #CPU_PortA_Speedo		;  -00000010-
	rts		    ; return from subroutine

InterruptVector_SpeedometerSignal:
	ldd  CPU_TimerInputCapture2_Speedometer
	stD *Temp5	    ; store D to RAM
	bsr  DetermineIfSpeedoSensorOnOrOff    ; call subroutine
	beq  L1687	    ; branch if equal (zero)
	fdiv		
	bsr  DetermineIfSpeedoSensorOnOrOff    ; call subroutine
	beq  L1687	    ; branch if equal (zero)
	fdiv		
	bsr  DetermineIfSpeedoSensorOnOrOff    ; call subroutine
	bne  JumpTo_ResetSpeedometerInterruptFlag    ; branch if not equal (not zero)
L1687:	ldd  Counter_SpeedSensorInterrupt2_HB    ; load d (a&b) with memory contents
	addd #0x0001	     ;	-00000000 00000001-
	stD *Counter_SpeedSensorInterrupt2_HB    ; store D to RAM
	bne  L1688	    ; branch if not equal (not zero)
	bset *b46_IPL2, #b46_bit0	; set bits
L1688:	inc  Counter_SpeedSensorInterrupt_HB
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	subd #0x0640	    ;  1600 dec
	ldaa BitFlags_56    ; load a with memory contents
	bcc  L1690	    ; branch if greater or equal
	bita #b56_BadSpeedo1	      ;  -00010000-
	bne  L1689	    ; branch if not equal (not zero)
	oraa #b56_BadSpeedo1	      ;  -00010000-
	bra  L1691	    ; branch

L1689:	anda #b56_BadSpeedo1 | b56_BadSpeedo2 | b56_BadASD | b56_AlternatorBits ; AND a with value -00011111-
	oraa #b56_BadSpeedo2	      ;  -00001000-
	staa BitFlags_56    ; store a into memory
	clra		    ; a = 0
	staa CruiseControlVar4	  ; store a into memory
	staa Counter_SomethingWithDistributor	 ; store a into memory
	staa Counter_TimerRegHalfOverflowBetweenSpeedoPulses	; store a into memory
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	addd #0x0053	;  83 decimal
	stD *VehicleSpeed_HB	; store D to RAM
JumpTo_ResetSpeedometerInterruptFlag:
	bra  ResetSpeedometerInterruptFlag    ; branch

L1690:	bita #b56_BadSpeedo1	      ;  -00010000-
	bne  L1701	    ; branch if not equal (not zero)
L1691:	adda #b56_bit5		;  -00100000-
	bcs  L1692	    ; branch if lower
	anda #~b56_BadSpeedo1	       ; AND a with value -11101111-
	staa BitFlags_56    ; store a into memory
	bra  ResetSpeedometerInterruptFlag    ; branch

L1692:	staa BitFlags_56    ; store a into memory
	ldab CruiseControlVar4	  ; load b with memory contents
	beq  L1695	    ; branch if equal (zero)
	bita #b56_BadSpeedo2	      ;  -00001000-
	bne  L1695	    ; branch if not equal (not zero)
	ldaa #0x3a	    ; load a with value -00111010-
	mul		    ; multiply (d=a*b)
	adca #0x00	    ;  -00000000-
	cmpa #0x03	    ; compare a with value -00000011-
	bcc  L1693	    ; branch if greater or equal
	ldaa #0x03	    ; load a with value -00000011-
L1693:	tab		    ; b = a
	ldaa Counter_SomethingWithDistributor	 ; load a with memory contents
	suba CruiseControlVar4
	bcc  L1694	    ; branch if greater or equal
	nega		    ; negate a (set high bit)
L1694:	sba		    ; subtract (a=a-b)
	bcs  L1696	    ; branch if lower
	bset *BitFlags_56, #b56_BadSpeedo2    ; set bits
L1695:	ldab Counter_SomethingWithDistributor	 ; load b with memory contents
	stab CruiseControlVar4	  ; store b into memory
L1696:	clra		    ; a = 0
	staa Counter_SomethingWithDistributor	 ; store a into memory
	ldd  Temp5	    ; load d (a&b) with memory contents
	bsr  DetermineNumberOfOverflowsBetweenSpeedoPulses_MM	 ; call subroutine
	ldaa Counter_TimerRegHalfOverflowBetweenSpeedoPulses	; load a with memory contents
	lsra		
	tab		    ; b = a
	oraa TimerOverflowsBetweenSpeedoPulses	  ; OR a with memory contents
	beq  L1697	    ; branch if equal (zero)
	stab TimerOverflowsBetweenSpeedoPulses	  ; store b into memory
	ldd  Temp5	    ; load d (a&b) with memory contents
	subd PreviousVehicleSpeed_HB	; d = d - memory contents
	bra  L1699	    ; branch

L1697:	ldd  Temp5	    ; load d (a&b) with memory contents
	subd PreviousVehicleSpeed_HB	; d = d - memory contents
	subd SpeedoSensorPulsewidth_HB    ; d = d - memory contents
	beq  L1700	    ; branch if equal (zero)
	asra		
	rorb		
	asra		
	rorb		
	subd #0x0000	     ;	-00000000 00000000-
	bne  L1698	    ; branch if not equal (not zero)
	incb		
L1698:	addd SpeedoSensorPulsewidth_HB    ; d = d + memory contents
L1699:	stD *SpeedoSensorPulsewidth_HB    ; store D to RAM
L1700:	ldd  Temp5	    ; load d (a&b) with memory contents
	stD *PreviousVehicleSpeed_HB	; store D to RAM
	clra		    ; a = 0
	staa Counter_TimerRegHalfOverflowBetweenSpeedoPulses	; store a into memory
ResetSpeedometerInterruptFlag:
	ldaa #CPU_TIFlag1_IC2SDSSignal	    ; clear the SDS flag
	staa CPU_TimerInterruptFlag1
	rti		    ; return from interrupt

L1701:	anda #~b56_BadSpeedo1	       ; AND a with value -11101111-
	staa BitFlags_56    ; store a into memory
	clra		    ; a = 0
	staa TimerOverflowsBetweenSpeedoPulses	  ; store a into memory
	ldd  #0x8ca0	    ; load d (a&b) with value -10001100 10100000-
	bra  L1699	    ; branch

DetermineNumberOfOverflowsBetweenSpeedoPulses_MM:
	subd PreviousVehicleSpeed_HB	; d = d - memory contents
	staa Temp7	    ; store a into memory
	ldaa Counter_TimerRegHalfOverflowBetweenSpeedoPulses	; load a with memory contents
	lsrd		    ; shift right (d=d/2)
	eorb Temp7	
	bpl  R1703	    ; branch if plus (hi bit 0)
	ldaa Counter_TimerRegHalfOverflowBetweenSpeedoPulses	; load a with memory contents
	inca		    ; increment a
	beq  L1702	    ; branch if equal (zero)
	staa Counter_TimerRegHalfOverflowBetweenSpeedoPulses	; store a into memory
L1702:	ldaa Counter_TimerRegHalfOverflowBetweenSpeedoPulses	; load a with memory contents
	lsra		
	cmpa TimerOverflowsBetweenSpeedoPulses	  ; compare a with memory contents
	bls  R1703	    ; branch if lower or same
	staa TimerOverflowsBetweenSpeedoPulses	  ; store a into memory
R1703:	rts		    ; return from subroutine

ControlCruiseServo1_MM:
	brclr *BitFlags_56, #b56_BadSpeedo1, L1704    ; branch if bit(s) clear
	sei		    ; disable interrupts
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	stD *Temp0	    ; store D to RAM
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	subd Temp0	    ; d = d - memory contents
	stD *VehicleSpeed_HB	; store D to RAM
	cli		    ; enable interrupts
L1704:	ldaa Timer_CountdownFromStartRunForAisFeedback	  ; load a with memory contents
	beq  L1707	    ; branch if equal (zero)
	brclr *BitFlags_54, #b54_JustStarted, L1705    ; branch if bit(s) clear
	clra		    ; a = 0
	ldx  EngineRpm_HB
	cpx  TargetIdleSpeed_HB
	bls  L1706	    ; branch if lower or same
L1705:	ldaa Timer_CountdownFromStartRunForAisFeedback	  ; load a with memory contents
	deca		    ; decrement a
L1706:	staa Timer_CountdownFromStartRunForAisFeedback	  ; store a into memory
	bra  L1708	    ; branch

L1707:	bset *BitFlags_54, #b54_JustStarted    ; set bits
L1708:	brclr *BitFlags_4f, #b4f_OffIdle, L1710    ; branch if bit(s) clear
L1709:	bclr *BitFlags_50, #b50_FallToIdle | b50_IdleSpeedMode	  ; clear bits
	rts		    ; return from subroutine

L1710:	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	lslb		
	adca #0x00	    ;  -00000000-
	ldab MPHREF_SwitchPointForDecelIdleAisControl	 ; load b with memory contents (data is 07)
	brset *BitFlags_50, #b50_IdleSpeedMode, L1711	 ; branch if bit(s) set
	brset *BitFlags_50, #b50_FallToIdle, L1711    ; branch if bit(s) set
	addb #0x03	    ;  -00000011-
L1711:	cba
	bls  L1709	    ; branch if lower or same
	ldab CONFIG_ConfigurationFlags	  ; load b with memory contents (data is 02)
	bitb #cfg_ATX		;  -00100000-
	bne  L1714	    ; branch if not equal (not zero)
	ldab AISMPH_RollingAisMaxSpeed	  ; load b with memory contents (data is 10)
	brclr *BitFlags_50, #b50_IdleSpeedMode, L1712	 ; branch if bit(s) clear
	addb #0x03	    ;  -00000011-
L1712:	cba
	bhi  L1714	    ; branch if speed is higher than Rolling AIS MAx
	ldd  TargetIdleSpeed_HB	; load d (a&b) with memory contents
	addd RPMDLT_RollingAisMinRpm	;  (data is 07)
	cmpD EngineRpm_HB    ; compare D
	bcs  L1714	    ; branch if lower
	brset *BitFlags_50, #b50_IdleSpeedMode, L1713	 ; branch if bit(s) set
	ldd  EngineRpm_HB    ; load d (a&b) with memory contents
	stD *TargetIdleSpeed_HB	; store D to RAM
L1713:	bclr *BitFlags_50, #b50_FallToIdle    ; clear bits
	bset *BitFlags_50, #b50_IdleSpeedMode	 ; set bits
	rts		    ; return from subroutine

L1714:	bset *BitFlags_50, #b50_FallToIdle    ; set bits
	bclr *BitFlags_50, #b50_IdleSpeedMode	 ; clear bits
	rts		    ; return from subroutine

ControlCruiseServo0_MM:
	brset *StartupSwitchMirror2, #sw2_CruiseOnOff, CruiseIsSwitchedOn    ; branch if bit(s) set
	ldaa CruiseStatus    ; load a with memory contents
	anda #0x88	    ; AND a with value -10001000-
	clrb		    ; b = 0
	stab CruiseSpeedSetpoint    ; store b into memory
	stab CruiseControlVar2	  ; store b into memory
	jmp  L1722	

CruiseIsSwitchedOn:
	brclr *CruiseStatus, #b2f_bit7, CruiseResumeSwitchPressed	 ; branch if bit(s) clear
	brset *StartupSwitchMirror2, #sw2_CruiseResume, CruiseResumeSwitchPressed    ; branch if bit(s) set
	bclr *CruiseStatus, #b2f_bit4    ; clear bits
CruiseResumeSwitchPressed:
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	lslb		
	adca #0x00	    ;  -00000000-
	staa Temp0	    ; store a into memory
	ldx  VehicleSpeed_HB
	cpx  LOSPCO_CruiseControlLowSpeedCutoutSpeed	;  (data is 0780)
	bcs  DropOutOfCruise	; branch if lower
	ldaa CONFIG_ConfigurationFlags	  ; load a with memory contents (data is 02)
	bita #cfg_ATX		;  -00100000-
	beq  L1717	    ; branch if equal (zero)
	brclr *StartupSwitchMirror2, #sw2_PNswitch, DropOutOfCruise    ; branch if bit(s) clear
	ldx  EngineRpm_HB
	cpx  #0xc0be	    ;  -11000000 10111110-
	bcc  DropOutOfCruise	; branch if greater or equal
	bra  L1721	    ; branch

L1717:	ldd  EngineRpm_HB    ; load d (a&b) with memory contents
	subd #0x8660	    ;  -10000110 01100000-
	bcs  L1718	    ; branch if lower
	subd #0x15e0	    ;  -00010101 11100000-
	bcc  DropOutOfCruise	; branch if greater or equal
	ldaa Temp0	    ; load a with memory contents
	suba CruiseSpeedSetpoint
	bcs  DropOutOfCruise	; branch if lower
	suba #0x08	    ;  -00001000-
	bcs  DropOutOfCruise	; branch if lower

L1718:	ldaa TimerOverflowsBetweenDistPulses	; load a with memory contents
	bne  L1720	    ; branch if not equal (not zero)
	ldab Temp0	    ; load b with memory contents
	ldaa DistributorFallingEdgePulsewidth_HB    ; load a with memory contents
	mul		    ; multiply (d=a*b)
	asld		    ; shift left (d=d*2)
	xgDY		    ; exchange D and Y
	ldaa #0x11	    ; load a with value -00010001-
	jsr  ScaleYbyA	    ; call subroutine
	xgDY		    ; exchange D and Y
	tsta		    ; test a
	beq  L1719	    ; branch if equal (zero)
	ldab #0xff	    ; load b with value -11111111-
L1719:	cmpb SCNVHI_CruiseControlForBrakeFlagManualTransmissionClutchDisable	; compare b with memory contents (data is ff)
	bcc  DropOutOfCruise	; branch if greater or equal
	cmpb SCNVLO_CruiseControlForBrakeFlagManualTransmissionClutchDisable	; compare b with memory contents (data is 52)
	bcs  DropOutOfCruise	; branch if lower
L1720:	brset *CruiseStatus, #b2f_bit7, L1721	 ; branch if bit(s) set
	brset *BitFlags_56, #b56_BadSpeedo2, DropOutOfCruise	; branch if bit(s) set
L1721:	brclr *StartupSwitchMirror2, #sw2_Brake, L1723    ; branch if bit(s) clear
DropOutOfCruise:
	clrb		    ; b = 0
	ldaa CruiseStatus    ; load a with memory contents
	anda #b2f_bit7 | b2f_bit4	    ; AND a with value -10010000-
L1722:	stab Timer_CruiseDecelerate    ; store b into memory
	bra  L1729	    ; branch

L1723:	ldaa PIA1_A_Buffer    ; load a with memory contents
	tab		    ; b = a
	eora PIA1_PortA_DataDirection
	anda #0x81	    ; AND a with value -10000001-
	beq  L1726	    ; branch if equal (zero)
	cmpa #0x80	    ; compare a with value -10000000-
	bcc  L1724	    ; branch if greater or equal
	rorb		
	rorb		
L1724:	ldaa #0x00	    ; load a with value -00000000-
	tstb		
	bpl  L1725	    ; branch if plus (hi bit 0)
	brset *CruiseStatus, #bit_bit7, ContinueCruise	  ; branch if bit(s) set
	ldd  #0x0f89	    ; load d (a&b) with value -00001111 10001001-
	jsr  ThrowNonCriticalError    ; call subroutine
	cmpD #0x0f08	    ; compare D -00001111 00001000-
	bne  L1726	    ; branch if not equal (not zero)
	clr  0x00,x	
	clr  0x02,x	
	bra  DropOutOfCruise	; branch

ContinueCruise:
	ldaa #0x07	    ; load a with value -00000111-
	ldab PIA1_PortA_DataDirection	 ; load b with memory contents
	andb #0x81	    ;  -10000001-
	bne  L1725	    ; branch if not equal (not zero)
	ldaa #0x7f	    ; load a with value -01111111-
L1725:	bita Counter_MainLoop
	bne  L1726	    ; branch if not equal (not zero)
	ldd  #0x0f10	    ; load d (a&b) with value -00001111 00010000-
	jsr  ThrowNonCriticalError    ; call subroutine
L1726:	ldaa CruiseStatus    ; load a with memory contents
	brset *StartupSwitchMirror2, #sw2_CruiseSet, L1732    ; branch if bit(s) set
	brclr *StartupSwitchMirror2, #sw2_CruiseResume, L1732    ; branch if bit(s) clear
	oraa #b2f_bit5	    ;  -00100000-
	ldab Timer_CruiseDecelerate    ; load b with memory contents
	incb		
	beq  L1727	    ; branch if equal (zero)
	stab Timer_CruiseDecelerate    ; store b into memory
L1727:	ldab Timer_CruiseDecelerate    ; load b with memory contents
	cmpb SETIME_CruiseControlNoSetupPulseWhenDecelTimerAboveThis	; compare b with memory contents (data is 37)
	bcs  L1730	    ; branch if lower
	cmpb SETIM1_CruiseControlNoSetupPulseWhenDecelTimerBelowThis	; compare b with memory contents (data is 52)
	bcc  L1728	    ; branch if greater or equal
	brset *CruiseStatus, #bit_bit7, L1730	 ; branch if bit(s) set
	oraa #b2f_bit2	    ;  -00000100-
	anda #~(b2f_bit0 | b2f_bit1)
	bra  L1729
L1728:	anda #~b2f_bit2	    ; AND a with value -11111011-
L1729:	oraa #b2f_bit7	    ;  -10000000-
L1730:	staa CruiseStatus    ; store a into memory
L1731:	jmp  L1750

L1732:	brset *CruiseStatus, #b2f_bit5, L1733    ; branch if bit(s) set
	jmp  L1746

L1733:	anda #0xdf	    ; AND a with value -11011111-
	staa CruiseStatus    ; store a into memory
	ldab Timer_CruiseDecelerate    ; load b with memory contents
	clr  Timer_CruiseDecelerate    ; zero byte at memory location
	cmpb #0x03	    ;  -00000011-
	bcs  L1731	    ; branch if lower
	brset *CruiseStatus, #bit_bit7, L1734	 ; branch if bit(s) set
	ldaa Temp0	    ; load a with memory contents
	suba CruiseSpeedSetpoint
	bcs  CruiseBumpUpSpeedBy2Mph	; branch if lower
	cmpa #0x04	    ; compare a with value -00000100-
	bls  CruiseBumpUpSpeedBy2Mph	; branch if lower or same
L1734:	bclr *BitFlags_56, #b56_BadSpeedo2    ; clear bits
	ldaa Temp0	    ; load a with memory contents
	staa CruiseSpeedSetpoint    ; store a into memory
	clra		    ; a = 0
	brset *CruiseStatus, #$%00000100, L1735    ; branch if bit(s) set
	staa CruiseControlVar6	  ; store a into memory
	staa Counter_Cruise    ; store a into memory
	bset *CruiseStatus, #$%00000001    ; set bits
	bsr  L1739	    ; call subroutine
L1735:	ldab CruiseStatus    ; load b with memory contents
	orab #0x10	    ;  -00010000-
	andb #0xf9	    ;  -11111001-
	bra  L1736	    ; branch

CruiseBumpUpSpeedBy2Mph:
	ldaa CruiseSpeedSetpoint    ; load a with memory contents
	adda #0x04	    ;  -00000100-
	staa CruiseSpeedSetpoint    ; store a into memory
	ldaa CRSVAR_CruiseControlVariableAdd	; load a with memory contents (data is 03)
	ldab CruiseStatus    ; load b with memory contents
	orab #0x40	    ;  -01000000-
	andb #0xfc	    ;  -11111100-
L1736:	andb #0x7f	    ;  -01111111-
	stab CruiseStatus    ; store b into memory
	ldab CruiseSpeedSetpoint    ; load b with memory contents
	cmpb MAXSET_CruiseControlMaxSetSpeedTimesTwo	; compare b with memory contents (data is aa)
	bcs  L1737	    ; branch if lower
	ldab MAXSET_CruiseControlMaxSetSpeedTimesTwo	; load b with memory contents (data is aa)
	bra  L1738	    ; branch

L1737:	cmpb MINSET_CruiseControlMinSetSpeedTimesTwo	; compare b with memory contents (data is 46)
	bcc  L1748	    ; branch if greater or equal
	clrb		    ; b = 0
L1738:	stab CruiseSpeedSetpoint    ; store b into memory
	bra  L1748	    ; branch

L1739:	ldaa CruiseSpeedSetpoint    ; load a with memory contents
	ldx  #SETPW_CruiseControlSetupPulseForSet_FromSpeed    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	bpl  L1740	    ; branch if plus (hi bit 0)
	ldab #0x7f	    ; load b with value -01111111-
L1740:	stab Temp1	    ; store b into memory
	ldaa MapValue	    ; load a with memory contents
	suba BaroPressure
	bcc  L1741	    ; branch if greater or equal
	tab		    ; b = a
	eorb #0x80	    ;  -10000000-
L1741:	bpl  L1742	    ; branch if plus (hi bit 0)
	lsla		    ; logical shift left a
	ldaa #0x80	    ; load a with value -10000000-
	sbca #0x00	    ;  -00000000-
L1742:	adda #0x80	    ;  -10000000-
	ldx  #RESTBL_CruiseControlAdditionalSetupPulseForResume_FromSpeedDifference    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	ldab Temp1	    ; load b with memory contents
	lslb		
	mul		    ; multiply (d=a*b)
	adca #0x00	    ;  -00000000-
	bpl  L1743	    ; branch if plus (hi bit 0)
	ldaa #0x7f	    ; load a with value -01111111-
L1743:	adda BitFlags_27
	bpl  R1744	    ; branch if plus (hi bit 0)
	bvs  L1745	    ; branch if no overflow
	clra		    ; a = 0
R1744:	rts		    ; return from subroutine

L1745:	ldaa #0x7f	    ; load a with value -01111111-
	rts		    ; return from subroutine

L1746:	brclr *StartupSwitchMirror2, #sw2_CruiseResume, L1750    ; branch if bit(s) clear
	bita #0x50	    ;  -01010000-
	bne  L1750	    ; branch if not equal (not zero)
	ldab CruiseSpeedSetpoint    ; load b with memory contents
	beq  L1750	    ; branch if equal (zero)
	bclr *BitFlags_56, #b56_BadSpeedo2    ; clear bits
	anda #0x7f	    ; AND a with value -01111111-
	oraa #0x50	    ;  -01010000-
	staa CruiseStatus    ; store a into memory
	bsr  L1739	    ; call subroutine
	staa CruiseControlVar3	  ; store a into memory
	ldaa CruiseSpeedSetpoint    ; load a with memory contents
	suba Temp0	
	bcs  L1749	    ; branch if lower
	ldx  #RESTBL2_CruiseControlAdditionalSetupPulseForResume_FromSpeedDifference2    ; load index with value
	jsr  Lookup4ByteTable	 ; call subroutine
	bmi  L1747	    ; branch if minus(hi bit 1)
	adda CruiseControlVar3
	bpl  L1748	    ; branch if plus (hi bit 0)
L1747:	ldaa #0x7f	    ; load a with value -01111111-
L1748:	staa CruiseControlVar3	  ; store a into memory
L1749:	bset *CruiseStatus, #$%00001000    ; set bits
L1750:	ldaa Counter_MainLoop	  ; load a with memory contents
	cmpa #0xf3	    ; compare a with value -11110011-
	bcc  L1753	    ; branch if greater or equal
	suba #0x84	    ;  -10000100-
	bcc  L1751	    ; branch if greater or equal
	ldaa Counter_MainLoop	  ; load a with memory contents
L1751:	tab		    ; b = a
	suba #0x42	    ;  -01000010-
	bcc  L1752	    ; branch if greater or equal
	tba		    ; a = b
L1752:	suba #0x0b	    ;  -00001011-
	bcc  L1752	    ; branch if greater or equal
	adda #0x0b	    ;  -00001011-
	beq  L1754	    ; branch if equal (zero)
L1753:	jmp  L1797

L1754:	clrb		    ; b = 0
	brclr *BitFlags_56, #b56_BadSpeedo1, CalculateVehicleSpeed    ; branch if bit(s) clear
	jmp  L1775	

CalculateVehicleSpeed:
	ldY #SpeedoSensorPulsewidth_HB    ; load Y index -00000000 00110101-
	ldx  #0xe800	    ; load index with value   - should be 0x6800?
	ldd  #0x036e	    ; load d (a&b) with value -00000011 01101110-
	brclr *TimerOverflowsBetweenSpeedoPulses, #$%11111111, L1755	; branch if bit(s) clear
	clrb		    ; b = 0
	clra		    ; a = 0
	brset *TimerOverflowsBetweenSpeedoPulses, #$%01000000, L1756	; branch if bit(s) set
	ldab #0x03	    ; load b with value -00000011-
	deY		    ; decrement Y
	ldx  #0x6ee8	    ; load index with value
L1755:	jsr  CalculateVehicleSpeedOrEngineRpms	  ; call subroutine
L1756:	ldx  VehicleSpeed_HB
	stx  Temp0	    ; store index into memory
	stD *VehicleSpeed_HB	; store D to RAM
	brset *CruiseStatus, #bit_bit7, L1757	 ; branch if bit(s) set
	brclr *CruiseStatus, #$%00000010, L1757    ; branch if bit(s) clear
	ldaa Counter_Cruise    ; load a with memory contents
	brclr *CruiseStatus, #$%00000001, L1759    ; branch if bit(s) clear
	cmpa CRMASK_CruiseMask	  ; compare a with memory contents (data is 11)
	bcc  L1758	    ; branch if greater or equal
	inca		    ; increment a
	staa Counter_Cruise    ; store a into memory
L1757:	bra  L1769	    ; branch

L1758:	bclr *CruiseStatus, #$%00000001    ; clear bits
	clra		    ; a = 0
	staa Counter_Cruise    ; store a into memory
L1759:	cmpa CRSCN1_CruiseComapreConstant1    ; compare a with memory contents (data is 15)
	bcs  L1765	    ; branch if lower
	ldab CruiseControlVar6	  ; load b with memory contents
	tba		    ; a = b
	bpl  L1760	    ; branch if plus (hi bit 0)
	negb		
L1760:	cmpb CRSCN2_CruiseComapreConstant2    ; compare b with memory contents (data is 06)
	bcs  L1764	    ; branch if lower
	ldab BitFlags_27    ; load b with memory contents
	adda CruiseControlVar
	bvc  L1761	    ; branch if overflow
	lsla		    ; logical shift left a
	ldaa #0x80	    ; load a with value -10000000-
	sbca #0x00	    ;  -00000000-
L1761:	staa CruiseControlVar	       ; store a into memory
	cmpa CRMSK2_CruiseMask2    ; compare a with memory contents (data is 07)
	bgt  L1762	    ; branch if greater
	cmpa CRMSK3_CruiseMask3    ; compare a with memory contents (data is f4)
	bge  L1764	    ; branch if greater or equal
	subb CRMSK4_CruiseMask4    ; subtract memory contents from b (data is 02)
	cmpb CRMSK5_CruiseMask5    ; compare b with memory contents (data is e2)
	bge  L1763	    ; branch if greater or equal
	ldab CRMSK5_CruiseMask5    ; load b with memory contents (data is e2)
	bra  L1763	    ; branch

L1762:	addb CRMSK7_CruiseMask7    ;  (data is 01)
	cmpb CRMSK6_CruiseMask6    ; compare b with memory contents (data is 1e)
	ble  L1763	    ; branch if less or equal
	ldab CRMSK6_CruiseMask6    ; load b with memory contents (data is 1e)
L1763:	stab BitFlags_27    ; store b into memory
	clra		    ; a = 0
	staa CruiseControlVar	       ; store a into memory
L1764:	bclr *CruiseStatus, #$%00000010    ; clear bits
	bra  L1769	    ; branch

L1765:	inca		    ; increment a
	staa Counter_Cruise    ; store a into memory
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	ldaa CruiseSpeedSetpoint    ; load a with memory contents
	lsla		    ; logical shift left a
	lsla		    ; logical shift left a
	sba		    ; subtract (a=a-b)
	adda SETDLT_CruiseControlSetDeltaControlPointForCableAdaptive	 ;  (data is 00)
	bmi  L1767	    ; branch if minus(hi bit 1)
	ldab CruiseControlVar6	  ; load b with memory contents
	bpl  L1766	    ; branch if plus (hi bit 0)
	comb		
	incb		
L1766:	cba
	ble  L1769	    ; branch if less or equal
	staa CruiseControlVar6	  ; store a into memory
	bra  L1769	    ; branch

L1767:	ldab CruiseControlVar6	  ; load b with memory contents
	bmi  L1768	    ; branch if minus(hi bit 1)
	comb		
	incb		
L1768:	cba
	bge  L1769	    ; branch if greater or equal
	staa CruiseControlVar6	  ; store a into memory
L1769:	ldd  Temp0	    ; load d (a&b) with memory contents
	subd VehicleSpeed_HB	; d = d - memory contents
	bne  L1770	    ; branch if not equal (not zero)
	clr  CruiseControlVar1	  ; zero byte at memory location
L1770:	stD *Temp0	    ; store D to RAM
	clra		    ; a = 0
	ldab CruiseControlVar1	  ; load b with memory contents
	bpl  L1771	    ; branch if plus (hi bit 0)
	deca		    ; decrement a
L1771:	addd Temp0	    ; d = d + memory contents
	asra		
	rorb		
	asld		    ; shift left (d=d*2)
	bcs  L1772	    ; branch if lower
	tsta		    ; test a
	beq  L1774	    ; branch if equal (zero)
	ldab #0x7f	    ; load b with value -01111111-
	bra  L1775	    ; branch

L1772:	cmpa #0xff	    ; compare a with value -11111111-
	beq  L1773	    ; branch if equal (zero)
	clrb		    ; b = 0
L1773:	sec		    ; set carry
L1774:	rorb
L1775:	stab CruiseControlVar1	  ; store b into memory
	brset *CruiseStatus, #$%00001000, L1778    ; branch if bit(s) set
	brset *CruiseStatus, #bit_bit7, L1776	 ; branch if bit(s) set
	ldaa Timer_CruiseDecelerate    ; load a with memory contents
	cmpa SETIME_CruiseControlNoSetupPulseWhenDecelTimerAboveThis	; compare a with memory contents (data is 37)
	bcs  L1779	    ; branch if lower
L1776:	ldaa #0x0f	    ; load a with value -00001111-
L1777:	oraa #0x80	    ;  -10000000-
	staa CruiseControlVar3	  ; store a into memory
L1778:	jmp  L1797

L1779:	ldx  #VACREG_CruiseControlVacRegularGainGurve_FromDeltaSpeed	; load index with value
	clrb		    ; b = 0
	ldaa CruiseSpeedSetpoint    ; load a with memory contents
	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	subd VehicleSpeed_HB	; d = d - memory contents
	bcc  L1781	    ; branch if greater or equal
	ldx  #VENTRG_CruiseControlVentRegularGainCurve_FromDeltaSpeed	 ; load index with value
	coma		
	comb		
	addd #0x0001	     ;	-00000000 00000001-
	stab Temp0	    ; store b into memory
	bclr *CruiseStatus, #$%01000000    ; clear bits
	tsta		    ; test a
	beq  L1780	    ; branch if equal (zero)
	bset *Temp0, #$%11111111    ; set bits
L1780:	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	tsta		    ; test a
	bne  L1776	    ; branch if not equal (not zero)
	cmpb VNTAB1_CruiseControlLimitToAMaxVent    ; compare b with memory contents (data is ff)
	bcc  L1776	    ; branch if greater or equal
	tba		    ; a = b
	ldab Temp0	    ; load b with memory contents
	cmpa VNTAB2_CruiseControlLimitToHalfMaxVent    ; compare a with memory contents (data is f0)
	bcs  L1784	    ; branch if lower
	ldaa #0x05	    ; load a with value -00000101-
	bra  L1777	    ; branch

L1781:	brclr *CruiseStatus, #$%01000000, L1782    ; branch if bit(s) clear
	ldx  #VACACC_CruiseControlVacAcceleratedGainCurve_FromDeltaSpeed    ; load index with value
	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
L1782:	tsta		    ; test a
	beq  L1783	    ; branch if equal (zero)
	ldab #0xff	    ; load b with value -11111111-
L1783:	cmpb ACLRST_CruiseControlDeltaSpeedToResetAccFlag    ; compare b with memory contents (data is 09)
	bcc  L1784	    ; branch if greater or equal
	bclr *CruiseStatus, #$%01000000    ; clear bits
L1784:	tba		    ; a = b
	jsr  Lookup4ByteTable	 ; call subroutine
	clra		    ; a = 0
	tstb		
	bpl  L1785	    ; branch if plus (hi bit 0)
	deca		    ; decrement a
L1785:	stD *Temp0	    ; store D to RAM
	ldx  #THGAIN_CruiseControlThrottleGainFactor_FromThrottle    ; load index with value
	ldaa TpsVolts	    ; load a with memory contents
	suba MINTHR_LowestSessionTPS
	bcc  L1786	    ; branch if greater or equal
	clra		    ; a = 0
L1786:	jsr  Lookup4ByteTable	 ; call subroutine
	staa Temp4	    ; store a into memory
	ldx  #SPGAIN_CruiseControlSpeedGainFactor_FromSpeed    ; load index with value
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	jsr  Lookup4ByteTable	 ; call subroutine
	adda Temp4
	staa Temp3	    ; store a into memory
	clra		    ; a = 0
	staa Temp2	    ; store a into memory
	ldab CruiseControlVar2	  ; load b with memory contents
	bpl  L1787	    ; branch if plus (hi bit 0)
	deca		    ; decrement a
L1787:	addd Temp0	    ; d = d + memory contents
	stD *Temp0	    ; store D to RAM
	clra		    ; a = 0
	ldab CruiseControlVar1	  ; load b with memory contents
	bpl  L1788	    ; branch if plus (hi bit 0)
	deca		    ; decrement a
L1788:	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	addd Temp0	    ; d = d + memory contents
	staa Temp0	    ; store a into memory
	bpl  L1789	    ; branch if plus (hi bit 0)
	coma		
	comb		
	addd #0x0001	     ;	-00000000 00000001-
L1789:	subd Temp2	    ; d = d - memory contents
	bcc  L1791	    ; branch if greater or equal
	addb Temp3	    ; b=b+memory contents
	ldaa Temp0	    ; load a with memory contents
	bpl  L1790	    ; branch if plus (hi bit 0)
	negb		
L1790:	stab CruiseControlVar2	  ; store b into memory
	bra  L1797	    ; branch

L1791:	clra		    ; a = 0
	staa CruiseControlVar2	  ; store a into memory
	ldaa Temp0	    ; load a with memory contents
	anda #0x80	    ; AND a with value -10000000-
	oraa VACTIM_CruiseControlVacuumTime    ;  (data is 01)
	ldab CruiseControlVar3	  ; load b with memory contents
	beq  L1792	    ; branch if equal (zero)
	bpl  L1797	    ; branch if plus (hi bit 0)
	tab		    ; b = a
	eorb CruiseControlVar3
	bpl  L1797	    ; branch if plus (hi bit 0)
L1792:	ldab TpsVolts	    ; load b with memory contents
	subb MINTHR_LowestSessionTPS	; b = b-memory contents
	bcc  L1793	    ; branch if greater or equal
	clrb		    ; b = 0
L1793:	tsta		    ; test a
	bpl  L1794	    ; branch if plus (hi bit 0)
	cmpb CLOTHR_CruiseControlDontVentIfThrottleBelowThis	; compare b with memory contents (data is 01)
	bcs  L1795	    ; branch if lower
	bra  L1796	    ; branch

L1794:	cmpb MAXTHR_CruiseControlDontVacIfThrottleAboveThis    ; compare b with memory contents (data is 50)
	bcs  L1796	    ; branch if lower
L1795:	clra		    ; a = 0
L1796:	staa CruiseControlVar3	  ; store a into memory
L1797:	ldaa PIA1_A_Buffer    ; load a with memory contents
	anda #~(pia1abuf_CruiseVent | pia1abuf_CruiseVacuum)	   ; AND a with value -01111110- Fixed this value
	bclr *CruiseStatus, #$%00001000    ; clear bits
	brset *CruiseStatus, #bit_bit7, L1798	 ; branch if bit(s) set
	ldab CruiseControlVar3	  ; load b with memory contents
	beq  L1799	    ; branch if equal (zero)
	bpl  L1800	    ; branch if plus (hi bit 0)
L1798:	oraa #pia1abuf_CruiseVent | pia1abuf_CruiseVacuum	   ;  -10000001-
L1799:	oraa #pia1abuf_CruiseVacuum	     ;	-00000001-
L1800:	staa PIA1_A_Buffer    ; store a into memory
	ldab CruiseControlVar3	  ; load b with memory contents
	beq  L1802	    ; branch if equal (zero)
	asld		    ; shift left (d=d*2)
	subb #0x02	    ;  -00000010-
	beq  L1801	    ; branch if equal (zero)
	lsrd		    ; shift right (d=d/2)
L1801:	stab CruiseControlVar3	  ; store b into memory
	rts		    ; return from subroutine

L1802:	brclr *CruiseStatus, #$%00000001, R1803    ; branch if bit(s) clear
	bset *CruiseStatus, #$%00000010    ; set bits
R1803:	rts		    ; return from subroutine

IncrementLoopCounters_MM:
	inc  Counter_MainLoop
	bne  L1805	    ; branch if not equal (not zero)
	ldaa #0xff	    ; load a with value -11111111-
	cmpa KeyOnOrEngineRunningTime	 ; compare a with memory contents
	beq  L1804	    ; branch if equal (zero)
	inc  KeyOnOrEngineRunningTime
L1804:	brset *BitFlags_54, #b54_FuelEngineNotRunning, L1805	; branch if bit(s) set
	bclr *BitFlags_AIS, #b0c_bit0 | b0c_bit1    ; clear bits
	cmpa EngineRunningTimeMaxFF    ; compare a with memory contents
	beq  L1805	    ; branch if equal (zero)
	inc  EngineRunningTimeMaxFF
L1805:	ldaa TimerOverflowsBetweenDistPulses	; load a with memory contents
	beq  L1806	    ; branch if equal (zero)
	bset *BitFlags_54, #b54_FuelEngineNotRunning | b54_Starting | b54_DisableNormalDwell	; set bits
	bclr *BitFlags_4f, #b4f_OpenLoop | b4f_O2Valid	  ; clear bits
	bclr *BitFlags_50, #b50_FuelCurveACToggle	; clear bits
	ldaa EngineRunningTimeMaxFF    ; load a with memory contents
	staa EngineRunningTimeBeforeStall    ; store a into memory
L1806:	ldaa Timer_AisChanges	 ; load a with memory contents
	inca		    ; increment a
	beq  R1807	    ; branch if equal (zero)
	staa Timer_AisChanges	 ; store a into memory
R1807:	rts		    ; return from subroutine

CALCULATE_RPM_SPEED_AND:
; if MAP is decreasing, then the RPM can be filtered. Not sure why, looks like it's not used (min delta RPM is FF)...
	ldaa MapValue	    ; load a with memory contents
	cmpa AverageMAPValue    ; compare a with memory contents
	bcc  L1808	    ; branch if greater or equal
	ldaa EngineRpm_HB    ; load a with memory contents
	staa Temp2	    ; store a into memory
	bsr  CalculateEngineRpm_MM    ; call subroutine
	stD *EngineRpm_HB    ; store D to RAM
	suba Temp2	
	bcs  R1809	    ; branch if lower
	cmpa DLTRPM2_RPMDeltaForRPMFilter    ; compare a with memory contents (data is ff)
	bcs  R1809	    ; branch if lower
	ldaa MapValue	    ; load a with memory contents
	staa AverageMAPValue    ; store a into memory
	rts		    ; return from subroutine

L1808:	bsr  CalculateEngineRpm_MM    ; call subroutine
	stD *EngineRpm_HB    ; store D to RAM
R1809:	rts		    ; return from subroutine
                            
DetectParkNeutral_MM:
	ldaa CONFIG_ConfigurationFlags	  ; load a with memory contents (data is 02)
	bita #cfg_ATX		;  -00100000-
	beq  L1813	    ; branch if equal (zero)
	brset *StartupSwitchMirror2, #sw2_PNswitch, L1810	 ; branch if bit(s) set
	brclr *BitFlags_AIS, #b0c_ATXInGear, R1812    ; branch if bit(s) clear
	bclr *BitFlags_AIS, #b0c_ATXInGear    ; clear bits
	bra  L1811	    ; branch

L1810:	brset *BitFlags_AIS, #b0c_ATXInGear, R1812    ; branch if bit(s) set
	bset *BitFlags_AIS, #b0c_ATXInGear    ; set bits
L1811:	bclr *BitFlags_50, #b50_FallToIdle    ; clear bits
	brset *BitFlags_54, #b54_FuelEngineNotRunning, R1812	; branch if bit(s) set
	bset *BitFlags_AIS, #b0c_ATXChngGear	; set bits
R1812:	rts		    ; return from subroutine

L1813:	bclr *BitFlags_AIS, #b0c_ATXInGear | b0c_ATXChngGear	; clear bits
	rts		    ; return from subroutine

CalculateEngineRpm_MM:
	ldY #DistributorFallingEdgePulsewidth_HB    ; load Y index -00000000 01001010-
	ldd  #0x0393	    ; load d (a&b) with value -00000011 10010011-
	ldx  #0x8700	    ; load index with value
	tst  TimerOverflowsBetweenDistPulses
	beq  CalculateVehicleSpeedOrEngineRpms	  ; branch if equal (zero)
	deY		    ; decrement Y
	ldd  #0x0003        ; load d (a&b) with value -00000000 00000011-
	ldx  #0x9387	    ; load index with value
CalculateVehicleSpeedOrEngineRpms:
	pshx		    ; pull index from stack
	ldX  0, Y	    ; load X indexed to Y
	fdiv
	stx  Temp0	    ; store index into memory
	pula		    ; pull a from stack
	pulb		    ; pull b from stack
	ldX  0, Y	    ; load X indexed to Y
	idiv		
	xgDX		    ; exchange D and X
	addd Temp0	    ; d = d + memory contents
	bcc  R1814	    ; branch if greater or equal
	ldd  #0xffff	    ; load d (a&b) with value -11111111 11111111-
R1814:	rts		    ; return from subroutine

CycleACClutch_MM:
	brset *Counter_MainLoop, #$%00000001, R1823	; branch if bit(s) set
	ldaa SwitchPortAccessReg    ; load a with memory contents
	tab		    ; b = a
	cmpa StartupSwitchMirror1    ; compare a with memory contents
	beq  L1815	    ; branch if equal (zero)
	pshb		    ; push b onto stack
	anda StartupSwitchMirror1    ; logical and a with memory contents
	eorb StartupSwitchMirror1
	andb StartupSwitchMirror2
	aba		    ; a=a+b
	pulb		    ; pull b from stack
L1815:	staa StartupSwitchMirror2    ; store a into memory
	stab StartupSwitchMirror1    ; store b into memory
	ldab ACClutchToggleVar	    ; load b with memory contents
	eora BitFlags_2e
	bita #b2e_AcClutch	    ;  -00010000-
	beq  L1820	    ; branch if equal (zero)
	brclr *StartupSwitchMirror2, #sw2_ACclutch, L1817    ; branch if bit(s) clear
	cmpb #0x30	    ;  -00110000-
	bcs  L1816	    ; branch if lower
	bset *BitFlags_2e, #b2e_AcClutch    ; set bits
	bclr *ACClutchToggleVar, #$%00000111    ; clear bits
L1816:	ldaa Counter_MainLoop	  ; load a with memory contents
	bita #0x1f	    ;  -00011111-
	bne  R1823	    ; branch if not equal (not zero)
	addb #0x08	    ;  -00001000-
	bcc  L1822	    ; branch if greater or equal
	rts		    ; return from subroutine

L1817:	brclr *ACClutchToggleVar, #$%00000111, L1818    ; branch if bit(s) clear
	tba		    ; a = b
	anda #0x07	    ; AND a with value -00000111-
	cmpa #0x05	    ; compare a with value -00000101-
	bls  L1819	    ; branch if lower or same
L1818:	cmpb #0xb8	    ;  -10111000-
	bcs  L1816	    ; branch if lower
	bclr *BitFlags_2e, #b2e_AcClutch    ; clear bits
L1819:	clrb		    ; b = 0
	bra  L1822	    ; branch

L1820:	brset *ACClutchToggleVar, #$%00000111, L1821    ; branch if bit(s) set
	incb
	stab ACClutchToggleVar	    ; store b into memory
L1821:	brset *BitFlags_2e, #b2e_AcClutch, L1816    ; branch if bit(s) set
	cmpb #0x60	    ;  -01100000-
	bcs  L1816	    ; branch if lower
	andb #0x07	    ;  -00000111-
	orab #0x60	    ;  -01100000-
L1822:	stab ACClutchToggleVar	    ; store b into memory
R1823:	rts		    ; return from subroutine

; ********************************************************
; Return interpolation value from a table
;    in = b for table X position,
;         x for table location in memory
;    out = both a and b are the Y return value

Lookup4ByteTable:
	ldY #0x0000	     ; load Y index -00000000 00000000-
	ldab 0x00,x	    ; load b with memory at index + value
	aby		    ; add b to y
	inx		    ; increment index (x=x+1)
	ldab #0x04	    ; load b with value -00000100-
	cmpa 0x00,x	    ; compare a with memory at index + value
	bhi  L1826	    ; branch if higher
L1824:	clrb		    ; b = 0
	bra  L1827	    ; branch

L1825:	abx		    ; add b to index
L1826:	deY		    ; decrement Y
	beq  L1824	    ; branch if equal (zero)
	cmpa 0x04,x	    ; compare a with memory at index + value
	bcc  L1825	    ; branch if greater or equal
	suba 0x00,x	
	psha		    ; push a onto stack
	ldab 0x02,x	    ; load b with memory at index + value
	mul		    ; multiply (d=a*b)
	xgDY		    ; exchange D and Y
	pula		    ; pull a from stack
	ldab 0x03,x	    ; load b with memory at index + value
	mul		    ; multiply (d=a*b)
	adca #0x00	    ;  -00000000-
	tab		    ; b = a
	aby		    ; add b to y
	xgDY		    ; exchange D and Y
L1827:	addb 0x01,x	    ; add memory at index + value to b
	tba		    ; a = b
	rts		    ; return from subroutine

; ********************************************************
; Scale Y by A, where a=0 = 0.0 and a=255 = 1.0
;*************************************************************
;
; Inputs: A = delta between data and next table point below
; Y = 16-bit slope of line
;
; Outputs:Y = interpolated value
;
; Pimarily used by the fueling system to calculate an
; interpolated point into one of the 5-byte tables. The base
; value of the break point will be added to the returned result
; of this routine to make the new interpolated return value.
;
;*************************************************************

ScaleYbyA:
	psha		    ; save a copy of the delta on the stack
	pshy		    ; save a copy of the slope on the stack
	pulb		    ; put the high byte of the slope into B
	mul		    ; multiply the delta by the slope high byte
	xgDY		    ; store the 16-bit result from D to Y
	pulb		    ; get the fractional byte of the slope
	pula		    ; retrieve stored copy of the delta
	mul		    ; multiply by the fraction, 16-bit result is D
	adca #0x00	    ; round off the result with the carry flag
	tab		    ; move A to B
	aby		    ; Add fraction result B to Y
	rts		    ; return from subroutine

; ********************************************************
; scales the 16-bit value at memory location X (not X itself)
; If a=1 adds 1.0 to scaling

ScaleXbyB_addingA_intoD:
	psha		    ; push a onto stack
	tba		    ; a = b
	ldY  0, X	    ; load Y indexed to X
	bsr  ScaleYbyA	    ; call subroutine
	pula		    ; pull a from stack
	tsta		    ; test a
	xgDY		    ; exchange D and Y
	beq  R1828	    ; branch if equal (zero)
	addd 0x00,x	
	bcc  R1828	    ; branch if greater or equal
	ldd  #0xffff	    ; load d (a&b) with value -11111111 11111111-
R1828:	rts		    ; return from subroutine

; ********************************************************
; X points to either the MAP or TPS 4-byte block.
; block of 4 bytes:   x+0: MSB of average value
;                     x+1: LSB of average value (scratch, never used)
;                     x+2: actual value (or faked if limpin)
;                     x+3: scaling factor for leanout or enrichment
; flow:
;       if scaling=0, save value into first byte, zero second, and return
;   otherwise:
;       scale average value by scaling factor


ProcessMapOrTpsBlockData:
	ldaa 0x03,x	    ; load a with current averaging factor
	bne  L1829	    ; branch if not equal (not zero)
	clrb		    ; b = 0
	ldaa 0x02,x	    ; load a with actual MAP or TPS value
	bra  L1830	    ; store average MAP or TPS value, in this case = same as actual, since the averaging factor = 0

L1829:	ldY  0, X	    ; load Y with the current average MAP or TPS
	bsr  ScaleYbyA	    ; scale the average MAP or TPS by the averaging factor
	pshy		    ; push the scaled current average MAP/TPS onto the stack
	ldd  0x02,x	    ; load a with the actual MAP value, b with the averaging factor
	mul		    ; multiply the MAP/TPS by the averaging factor, product ends up in D
	tSY		    ; load Y with the address of the LB of the scaled current average MAP value
	subD  0, Y	    ; subtract scaled current average from the product, delta stays in D
	puly		    ; get scaled current average from the stack (just to clear the stack)
	addd 0x00,x         ; add the scaled current average to the delta
L1830:	std  0x00,x	    ; store the new average to memory
	rts		    ; return from subroutine

DetermineNumberOfOverflowsBetweenDistributorPulses_MM:
	subd LastDistributorFallingEdgeTime    ; d = d - memory contents
	staa Temp5	    ; store a into memory
	ldaa Counter_TimerPastHalfwayBetweenDistPulses	  ; load a with memory contents
	lsrd		    ; shift right (d=d/2)
	eorb Temp5	
	bpl  L1831	    ; branch if plus (hi bit 0)
	ldaa Counter_TimerPastHalfwayBetweenDistPulses	  ; load a with memory contents
	inca		    ; increment a
	beq  L1831	    ; branch if equal (zero)
	staa Counter_TimerPastHalfwayBetweenDistPulses	  ; store a into memory
L1831:	ldaa Counter_TimerPastHalfwayBetweenDistPulses	  ; load a with memory contents
	lsra		
	cmpa TimerOverflowsBetweenDistPulses	; compare a with memory contents
	bcs  R1832	    ; branch if lower
	staa TimerOverflowsBetweenDistPulses	; store a into memory
R1832:	rts		    ; return from subroutine

InterruptVector_PIA_Signal:
	bsr  IgnitionFeedOnOffTracking	  ; call subroutine
	rti		    ; return from interrupt

IgnitionFeedOnOffTracking:
	ldd  #0x5a5a	    ; load d (a&b) with value -01011010 01011010-
	stD *L0000	    ; store D to RAM
	ldab PIA2_PortB_DataDirection	 ; load b with memory contents
	orab #pia2b_bit6	    ;  -01000000-
	stab PIA2_PortB_DataDirection	 ; store b into memory
	ldaa #0x17	    ; load a with value -00010111-
	ldab TimerOverflowsBetweenDistPulses	; load b with memory contents
	cmpb #0x02	    ;  -00000010-
	bcs  L1833	    ; branch if lower
	ldaa #0x09	    ; load a with value -00001001-
L1833:	staa CountdownTimerFromKeyOn	; store a into memory
	ldaa PIA2_PortB_ControlRegister    ; load a with memory contents
	anda #~pia2b_InjectorDriverSense	  ; AND a with value -11111110-
	staa PIA2_PortB_ControlRegister
	ldaa PIA1_PortB_ControlRegister    ; load a with memory contents
	anda #~pia1b_bit0	   ; AND a with value -11111110-
	staa PIA1_PortB_ControlRegister
	ldaa PIA2_PortB_DataDirection	 ; load a with memory contents
	ldaa PIA1_PortB_DataDirection	 ; load a with memory contents
	rts		    ; return from subroutine

GetControlFeedback_DetermineIfShutdownRequired_MM:
	ldx  #PIA2_PortB_DataDirection	  ; load index with value
	bset  1, X, #pia2b_bit2    ; bit set
	brclr *BitFlags_2e, #b2e_bit3, L1842	; branch if bit(s) clear
	bra  L1836	    ; branch

L1834:	ldd  CPU_TimerCounterRegHigh
	addd #0x07d0	    ;  add 2ms (2000us)
L1835:	cmpD CPU_TimerCounterRegHigh	; compare D
	bpl  L1835	    ; branch if plus (hi bit 0)
L1836:	ldaa PIA2_PortB_ControlRegister    ; load a with memory contents
	oraa #pia2b_InjectorDriverSense 	 ;  -00000001-
	staa PIA2_PortB_ControlRegister
	ldaa PIA1_PortB_ControlRegister    ; load a with memory contents
	oraa #pia1b_bit0	  ;  -00000001-
	staa PIA1_PortB_ControlRegister
	brclr  0, X, #pia2b_OC1Toggle, L1838    ; branch if bit(s) clear
	bclr *BitFlags_2e, #b2e_bit3	; clear bits
L1837:	clr  CountdownTimerFromKeyOn	; zero byte at memory location
	cli		    ; enable interrupts
	bclr  0, X, #pia2b_bit6    ; bit clear
	rts		    ; return from subroutine

L1838:	bclr  0, X, #pia2b_AlternatorField    ; bit clear
	ldaa BatteryVolts    ; load a with memory contents
	cmpa #0xc2	    ; compare a with value -11000010-
	bcs  L1839	    ; branch if lower
	ldd  #0x0830	    ; load d (a&b) with value -00001000 00110000-
	jsr  ThrowNonCriticalError    ; call subroutine
	ldx  #PIA2_PortB_DataDirection	  ; load index with value
L1839:	ldab 0x00,x	    ; load b with memory at index + value
	bitb #0x07	    ;  -00000111-
	bne  L1837	    ; branch if not equal (not zero)
	ldaa CountdownTimerFromKeyOn	; load a with memory contents
	bne  L1840	    ; branch if not equal (not zero)
	ldaa #0x02	    ; load a with value -00000010-
L1840:	deca		    ; decrement a
	beq  Shutdown_Routine	 ; branch if equal (zero)
	staa CountdownTimerFromKeyOn	; store a into memory
L1841:	bclr  0, X, #pia2b_bit6    ; bit clear
	rts		    ; return from subroutine

L1842:	ldaa CountdownTimerFromKeyOn	; load a with memory contents
	bne  L1843	    ; branch if not equal (not zero)
	brset  0, X, #pia2b_OC1Toggle, L1841    ; branch if bit(s) set
	ldd  #0x5a5a	    ; load d (a&b) with value -01011010 01011010-
	stD *L0000	    ; store D to RAM
	ldaa #0x17	    ; load a with value -00010111-
	ldab TimerOverflowsBetweenDistPulses	; load b with memory contents
	cmpb #0x02	    ;  -00000010-
	bcs  L1844	    ; branch if lower
	ldaa #0x09	    ; load a with value -00001001-
	bra  L1844	    ; branch

L1843:	cmpa #0x17	    ; compare a with value -00010111-
	beq  L1844	    ; branch if equal (zero)
	brset  0, X, #pia2b_OC1Toggle, L1836    ; branch if bit(s) set
L1844:	deca		    ; decrement a
	beq  L1845	    ; branch if equal (zero)
	staa CountdownTimerFromKeyOn	; store a into memory
	bset  0, X, #pia2b_bit6    ; bit set
	rts		    ; return from subroutine

L1845:	sei		    ; disable interrupts
	jsr  CaculateChecksum	 ; call subroutine
	sei		    ; disable interrupts
	jsr  CountRamValuesFrom02to2e    ; call subroutine
	stD *L0000	    ; store D to RAM
	ldx  #PIA2_PortB_DataDirection	  ; load index with value
	bclr  0, X, #pia2b_bit6 | pia2b_AlternatorField    ; bit clear
	ldd  CPU_TimerCounterRegHigh
	addd #0x09c4	    ;  add 2.5ms (2500us)
L1846:	brclr  0, X, #pia2b_OC1Toggle, L1847    ; branch if bit(s) clear
	jmp  L1834

L1847:	cmpD CPU_TimerCounterRegHigh	; compare D
	bpl  L1846	    ; branch if plus (hi bit 0)
	ldaa PIA2_PortB_DataDirection	 ; load a with memory contents
	bita #0x07	    ;  -00000111-
	beq  Stop_Routine    ; branch if equal (zero)
	bset *BitFlags_2e, #b2e_bit3	; set bits
	jmp  L1837

Shutdown_Routine:
	sei		    ; disable interrupts
	jsr  CountRamValuesFrom02to2e    ; call subroutine
	stD *L0000	    ; store D to RAM
Stop_Routine:
	ldaa #0x10	    ; load a with value -00010000-
	tap		    ; transfer a to p
	clra		    ; a = 0
	staa CPU_SerialControl2
	deca		    ; decrement a
	staa CPU_PortD
	staa CPU_PortD_DataDirection
	ldd  #0xf8f0	    ; load d (a&b) with value -11111000 11110000-
	std  CPU_OutputCompare1Mask
	ldd  #0x8020	    ; load d (a&b) with value -10000000 00100000-
	staa CPU_TimerForceCompare
	stab CPU_SerialPeripheralControl    ; store b into memory
	ldd  #0xcfff	    ; load d (a&b) with value -11001111 11111111-
	 
	 ; skipping past assembler problem:
	 .byte 0xdd, 0xfe		;  stD *STOPInstruction    ; store D to RAM

	ldaa CPU_SysConfigOptionReg    ; load a with memory contents
	anda #0xf7	    ; AND a with value -11110111-
	staa CPU_SysConfigOptionReg
	clra		    ; a = 0
	staa PIA1_PortA_ControlRegister
	staa PIA1_PortA_DataDirection
	staa PIA1_PortB_ControlRegister
	staa PIA1_PortB_DataDirection
	staa PIA2_PortA_ControlRegister
	staa PIA2_PortA_DataDirection
	staa PIA2_PortB_ControlRegister
	staa PIA2_PortB_DataDirection
	ldaa PIA1_PortA_DataDirection	 ; load a with memory contents
	 ; another small assembler problem:
	 .byte 0x7e, 0x00, 0xfe 	; jmp  STOPInstruction

LookupAndKeepSmallerBoostGoal:
;
; Temp4 stores the boost target for the boost control routine.
;
	jsr  Lookup4ByteTable	 ; call subroutine
	cmpa Temp4	    ; compare a with memory contents
	bcc  R1848	    ; branch if greater or equal
	staa Temp4	    ; store a into memory
R1848:	rts		    ; return from subroutine

CalcTargetBoost_MM:
;
; This routine only looks up and stores the target boost
;
	ldaa ATMOffset	    ; load a with memory contents
	cmpa #0x11	    ; compare a with value -00010001-
	beq  R1849	    ; branch if equal (zero)
	cmpa #0x14	    ; compare a with value -00010100-
	bne  GetBoostTargetFromTables    ; branch if not equal (not zero)
R1849:	rts		    ; return from subroutine

GetBoostTargetFromTables:
	ldx  #WSGRPM_AllowedBoost_FromRpm    ; load the "hi" boost table
	ldaa EngineRpm_HB    ; load a with memory contents
	jsr  Lookup4ByteTable	 ; call subroutine
	staa Temp4	    ; store a into memory
	ldx  #WSGTIM_AllowedBoost_FromTime    ; load index with value
	ldaa Timer_BoostTimer	 ; load a with memory contents
	bsr  LookupAndKeepSmallerBoostGoal    ; call subroutine
	ldx  #WSGCLT_AllowedBoost_FromTemp    ; load index with value
	ldaa CoolantTemp    ; load a with memory contents
	bsr  LookupAndKeepSmallerBoostGoal    ; call subroutine
	ldx  #WSGCHG_AllowedBoost_FromChargeTemp    ; load index with value
	ldaa ChargeTemp	; load a with memory contents
	bsr  LookupAndKeepSmallerBoostGoal    ; call subroutine
	ldx  #MXSBST_AllowedBoost_FromSpeed; load index with value
	ldd  VehicleSpeed_HB	; load d (a&b) with memory contents
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	asld		    ; shift left (d=d*2)
	bsr  LookupAndKeepSmallerBoostGoal    ; call subroutine
	brset *BitFlags_4f, #b4f_FullThrottle, CheckBoostSwitch ; if WOT, don't load the Part throttle boost limit table...
	ldx  #WSGPRT_AllowedBoostPartThrottle_FromThrottle    ; load index with value
	ldaa TpsVolts	    ; load a with memory contents
	suba MINTHR_LowestSessionTPS
	bcc  L1851	    ; branch if greater or equal
	clra		    ; a = 0
L1851:	bsr  LookupAndKeepSmallerBoostGoal    ; call subroutine

CheckBoostSwitch:
; the switchable boost code uses a constant for the "lo" boost setting
; if the boost switch is enabled (set to "hi" boost), the code ignores the "lo" constant
; the code first checks to see if the switchable boost option is even enabled...

; here, I check to see if the switchable boost is enabled or not, if not just skip to StoreBoostTarget...
	ldaa OPTN1_CalCustomOptionConfigFlags1
	bita #opt_SwBoost ; check if switchable boost is enabled
        beq  StoreBoostTarget ;skip looking at the switch state completely

	ldab SwitchPortAccessReg    ; load b with memory contents
	bita #opt_SwBstPol ; check the switch polarity
	beq  Polarity_Lo

Polarity_Hi:
	bitb BSTSWS_HighBoostSwitchSelect
	beq  LoadLoBoostAndLookup	    ; branch if equal (zero)
	bra  StoreBoostTarget

Polarity_Lo:
	bitb BSTSWS_HighBoostSwitchSelect
	bne  LoadLoBoostAndLookup	    ; branch if not equal (not zero)
	bra  StoreBoostTarget

LoadLoBoostAndLookup:
	ldaa LOWBST_AllowedBoostLo    ; "lo" boost constant
        bsr  LookupAndKeepSmallerBoostGoal
        
; add code to lookup specific boost target while staging
LoadStagingBoostAndLookup:
        ldx  #Turbonator_Flags
        brclr 0x00, x, #Turbonator_Staging, StoreBoostTarget 	 ; don't do anything unless we're staging, normal spark
        ldaa STGBST_AllowedBoostDuringStaging    ; staging boost constant
        bsr  LookupAndKeepSmallerBoostGoal

StoreBoostTarget:
        ldaa Temp4	    ; load a with the boost target (stored by LookupAndKeepSmallerBoostGoal)
	adda BaroPressure
	bcc  L1853	    ; branch if greater or equal
	ldaa #0xff	    ; load a with value -11111111-
L1853:	staa BoostTarget    ; store a into memory - this is the MAP target
	rts                 ; this is new, I want to separate the boost lookup from the WG control...


CalcWGDutyCycle_MM:
        ldaa OPTN2_CalCustomOptionConfigFlags2    ; load a with memory contents (data is 9f)
        bita #opt_T2BC          ;  -00000001-
        beq  L2855          ; branch if equal (zero)
        jmp  CalcWGDutyCycleT1

L2855:  jmp  CalcWGDutyCycleT2

CalcWGDutyCycleT1:
	brset *BitFlags_54, #b54_FuelEngineNotRunning, WGDC_ClearWGDutyCycleVars	; branch if bit(s) set
        ldaa BoostTarget
        staa Temp3
	ldaa Counter_MainLoop	  ; load a with memory contents
	ldx  #Cylinder2Retard	 ; load index with value
WGDC_LookAtCylRetards:	
        ldab 0x00,x	    ; load b with memory at index + value
	beq  L1856    ; branch if equal (zero)
	bita ARCMSK_AdaptiveRetardCounterMask	 ;  (data is 3f)
	bne  L2858	    ; branch if not equal (not zero)
	ldaa CoolantTemp    ; load a with memory contents
	cmpa ARMINT_AdaptiveRetardMinimumTemp	 ; compare a with memory contents (data is a6)
	bls  WGDC_Clear5psiBoostTimer	    ; branch if lower or same
	ldaa Timer_Over5PsiBoostMaxFF	 ; load a with memory contents
	inca		    ; increment a
	cmpa ARTM5P_AdaptiveRetardTimeOver5psiBoost    ; compare a with memory contents (data is 0c)
	bcs  WGDC_Store5psiBoostTimer	    ; branch if lower
	sei		    ; disable interrupts
	ldaa AdaptiveRetardIndex    ; load a with memory contents
	adda ARINDX_AdaptiveRetardIndexBase_80	  ;  (data is 80)
	bcc  L1855	    ; branch if greater or equal
	ldaa #0xff	    ; load a with value -11111111-
L1855:	staa AdaptiveRetardIndex    ; store a into memory
	cli		    ; enable interrupts
	bra  WGDC_Clear5psiBoostTimer	    ; branch

L1856:
	inx		    ; increment index (x=x+1)
	cpx  #Cylinder4Retard	 ;  -00000000 10100100-
	bls  WGDC_LookAtCylRetards	    ; branch if lower or same
	bita ARCMS2_AdaptiveRetardCounterMask2_00    ;	(data is 00)
	bne  L2858	    ; branch if not equal (not zero)
	ldaa Timer_Over5PsiBoostMaxFF	 ; load a with memory contents
	suba ARCMS3_AdaptiveRetardCounterMask3_FF    ;	(data is ff)
	bcc  WGDC_Store5psiBoostTimer	    ; branch if greater or equal
WGDC_Clear5psiBoostTimer:
	clra		    ; a = 0
WGDC_Store5psiBoostTimer:
	staa Timer_Over5PsiBoostMaxFF	 ; store a into memory
L2858:	ldaa BaroPressure    ; load a with memory contents
	adda MAPPT2_WastegateDutyCycleMapSwitchPoint2    ;  (data is 0a)
	cmpa MapValue	    ; compare a with memory contents
	bls  WGDC_CalculateWGDutyCycleVars	    ; branch if lower or same
WGDC_ClearWGDutyCycleVars:
	clra		    ; a = 0
	staa WastegateDutyCycleIncreaseFromKnock    ; store a into memory
	jsr  CallAndReturn1    ; call subroutine
	staa CurrentWastegateDutyCycle	 ; store a into memory
	ldab Counter_MainLoop	  ; load b with memory contents
	bitb #0x1f	    ;  -00011111-
	bne  R2860	    ; branch if not equal (not zero)
	ldaa Timer_BoostTimer	 ; load a with memory contents
	beq  R2860	    ; branch if equal (zero)
	deca		    ; decrement a
	staa Timer_BoostTimer	 ; store a into memory
R2860:	rts		    ; return from subroutine

WGDC_AdjustWGDutyCycle:
        bmi  LD7DB          ; branch if minus(hi bit 1)
        adda Temp4
        bcs  LD7D7          ; branch if lower
        cmpa #0xc8          ; compare a with value -11001000-
        bls  LD7E0          ; branch if lower or same
LD7D7:  ldaa #0xc8          ; load a with value -11001000-
        bra  LD7E0          ; branch

LD7DB:  adda Temp4
        bcs  LD7E0          ; branch if lower
        clra                ; a = 0
LD7E0:  staa Temp4          ; store a into memory
        rts                 ; return from subroutine

WGDC_CalculateWGDutyCycleVars:
	ldab Counter_MainLoop	  ; load b with memory contents
	bitb #0x1f	    ;  -00011111-
	bne  WGDC_LookupWGDutyCycleBase	    ; branch if not equal (not zero)
	ldab EngineRpm_HB    ; load b with memory contents
	cmpb RPMBST_MinimumRpmToTrackBoostCreep    ; compare b with memory contents (data is 6a)
	bcs  WGDC_LookupWGDutyCycleBase	    ; branch if lower
	ldaa Timer_BoostTimer	 ; load a with memory contents
	inca		    ; increment a
	beq  WGDC_LookupWGDutyCycleBase	    ; branch if equal (zero)
	staa Timer_BoostTimer	 ; store a into memory
	ldaa Temp3	    ; load a with boost target temp
	suba BaroPressure
	bcc  WGDC_LookupWGDutyCycleBase	    ; branch if greater or equal
	clra		    ; a = 0
WGDC_LookupWGDutyCycleBase:
        ldx  #DCWOT_FullThrottleWastegateDutyCycle_C8is100Percent_FromMap    ; load index with value
        jsr  Lookup4ByteTable               ; call subroutine
        staa Temp4        ; store a into memory
        ldaa EngineRpm_HB                ; load a with memory contents
        ldx  #DCWADJ_FullThrottleWastegateDutyCycleAdjustment_FromRpm    ; load index with value
        jsr  Lookup4ByteTable               ; call subroutine
        bsr  WGDC_AdjustWGDutyCycle

; instead of the delta to boost goal lookup, change this to an overshoot vs. rpm lookup
; if the actual boost is <= the boost target + overshoot, then set the DC to max (0xC8)
; this should help get the turbo up to boost and then switch over to the adaptives to 
; maintin the boost.
; 
        ldaa Temp3    ; load a with boost target
        suba MapValue
        bcc  LD838
        clra  ; if MAP is higher than boost target, set lookup reference to 0
LD838:  ldx  #DCWBST_FullThrottleWastegateDutyCycleAdjustment_FromBoostTarget        ; load index with value
        jsr  Lookup4ByteTable    ; call subroutine
        bsr  WGDC_AdjustWGDutyCycle
        brclr *BitFlags_55, #b55_BoostOver5psi, L1867	 ; branch if bit(s) clear
	bclr *BitFlags_55, #b55_BoostOver5psi	 ; clear bits
	ldab WastegateDutyCycleIncreaseFromKnock    ; load b with memory contents
	addb KDCINC_WastegateDutyCycleIncreaseStepWhenKnocking	  ;  (data is 08)
	bcc  L1865	    ; branch if greater or equal
	ldab #0xff	    ; load b with value -11111111-
L1865:	ldaa KDCMAX_WastegateDutyCycleIncreaseMaxWhenKnocking	 ; load a with memory contents (data is 3c)
	cba
	bcs  L1866	    ; branch if lower
	ldaa KDCMIN_WastegateDutyCycleIncreaseMinWhenKnocking	 ; load a with memory contents (data is 10)
	cba		
	bcs  WGDC_StoreWGDutyCycleFromKnock	    ; branch if lower
L1866:	tab		    ; b = a
	bra  WGDC_StoreWGDutyCycleFromKnock	    ; branch

L1867:	ldab Counter_MainLoop	  ; load b with memory contents
	bitb DECTIM_TimeScaleFor_DCDECK    ;  (data is 01)
	bne  L1869	    ; branch if not equal (not zero)
	ldab WastegateDutyCycleIncreaseFromKnock    ; load b with memory contents
	subb DCDECK_WastegateDutyCycleDecrementWhenSparkStillDerated	; subtract memory contents from b (data is 02)
	bcc  WGDC_StoreWGDutyCycleFromKnock	    ; branch if greater or equal
	clrb		    ; b = 0
WGDC_StoreWGDutyCycleFromKnock:
	stab WastegateDutyCycleIncreaseFromKnock    ; store b into memory
L1869:	ldaa Temp3	    ; load a with memory contents
	ldab BaroPressure    ; load b with memory contents
	addb MAPPT_WastegateDutyCycleMapSwitchPoint    ;  (data is 2d) ~7.75psi boost
	bcc  WGDC_SelectAdaptiveWGCell	  ; branch if greater or equal
	ldab #0xff	    ; load b with value -11111111-
WGDC_SelectAdaptiveWGCell:
	ldx  #DCCOR1_AdaptiveWastegateCellBelowMAPPT    ; load index with value
	cba		
	bcs  WGDC_LoadAdaptiveWGCell	    ; branch if lower
	inx		    ; increment index (x=x+1)
	ldab EngineRpm_HB    ; load b with memory contents
	cmpb DCRPM1_WastegateDutyCycleRpmBoundary1    ; compare b with memory contents (data is 83) ~4200rpm
	bcs  WGDC_LoadAdaptiveWGCell	    ; branch if lower
	inx		    ; increment index (x=x+1)
	cmpb DCRPM2_WastegateDutyCycleRpmBoundary2    ; compare b with memory contents (data is 96) ~4800rpm
	bcs  WGDC_LoadAdaptiveWGCell	    ; branch if lower
	inx		    ; increment index (x=x+1)
	cmpb DCRPM3_WastegateDutyCycleRpmBoundary3    ; compare b with memory contents (data is a9) ~5400rpm
	bcs  WGDC_LoadAdaptiveWGCell	    ; branch if lower
	inx		    ; increment index (x=x+1)
WGDC_LoadAdaptiveWGCell:
	ldab 0x00,x	    ; load b with memory at index + value
        brset *Turbonator_Flags, #Turbonator_FuelOff, WGDC_ClearBoostErrTimer    ; branch if bit(s) set
        brset *Turbonator_Flags, #Turbonator_SparkCut, WGDC_ClearBoostErrTimer    ; branch if bit(s) set
	suba MapValue
	bhi  WGDC_BoostIsBelowTarget	    ; branch if higher
WGDC_BoostIsAboveTarget:
	brset *BitFlags_52, #b52_WGDC, WGDC_DecrementWGAdaptive    ; branch needs to change for T2 style WG control
	bset *BitFlags_52, #b52_WGDC    ; set bits
	bra  WGDC_ClearBoostErrTimer	    ; branch
WGDC_DecrementWGAdaptive:
	nega		    ; negate a (set high bit)
	cmpa MPDEL1_IncCounterWhenDeltaMapBelowThis    ; compare a with memory contents (data is 01)
	bcs  WGDC_ClearBoostErrTimer	    ; branch if lower
	ldaa MapValue	    ; load a with memory contents
	suba AverageMAPValue
	bcc  L1871	    ; branch if greater or equal
	nega		    ; negate a (set high bit)
L1871:	cmpa MPFLOR_StopAdaptiveWGWhenDeltaMapIsLessThanThis	 ; compare a with memory contents (data is 01)
	bhi  WGDC_ClearBoostErrTimer	    ; branch if higher
	ldaa Timer_BoostErrTimer    ; load a with memory contents
	inca		    ; increment a
	cmpa DECPT_AdaptiveDecAfterThisTime    ; compare a with memory contents (data is 20)
	bcs  WGDC_StoreBoostErrTimer	    ; branch if lower
	cmpb DECLIM_LowerLimitOnWastegateDutyCycleCorrection	; compare b with memory contents (data is 44)
	bls  WGDC_ClearBoostErrTimer	    ; branch if lower or same
	decb		
	bra  WGDC_UpdateAdaptiveWGControlMemory    ; branch
WGDC_BoostIsBelowTarget:
        brclr *BitFlags_52, #b52_WGDC, WGDC_IncrementWGAdaptive    ; branch if bit(s) clear
	bclr *BitFlags_52, #b52_WGDC    ; clear bits
	bra  WGDC_ClearBoostErrTimer	    ; branch
WGDC_IncrementWGAdaptive:
	cmpa MPROOF_StopAdaptiveWGWhenMapIsThisCloseToBoostTarget    ; compare a with memory contents (data is 00)
	bcs  WGDC_ClearBoostErrTimer	    ; branch if lower
	ldaa TpsVolts	    ; load a with memory contents
	suba MINTHR_LowestSessionTPS
	bls  WGDC_ClearBoostErrTimer	    ; branch if lower or same
	cmpa TPSLIM_UpdateAdaptiveWGTPSUpperLimit    ; compare a with memory contents (data is 66)
	bcs  WGDC_ClearBoostErrTimer	    ; branch if lower
	ldaa MapValue	    ; load a with memory contents
	suba AverageMAPValue
	bcc  L1873	    ; branch if greater or equal
	nega		    ; negate a (set high bit)
L1873:	cmpa MPDEL2_IncCounterWhenDeltaMapBelowThis2    ; compare a with memory contents (data is 01)
	bhi  WGDC_ClearBoostErrTimer	    ; branch if higher
	ldaa WastegateDutyCycleIncreaseFromKnock    ; load a with memory contents
	bne  WGDC_ClearBoostErrTimer	    ; branch if not equal (not zero)
	ldaa EngineRpm_HB    ; load a with memory contents
	cmpa DCRPML_NoWastegateDutyCycleCorrectionBelowThisRpm	  ; compare a with memory contents (data is 54)
	bcs  WGDC_ClearBoostErrTimer	    ; branch if lower
	ldaa Timer_BoostErrTimer    ; load a with memory contents
	inca		    ; increment a
	cmpa INCPT_AdaptiveIncAfterThisTime    ; compare a with memory contents (data is 20)
	bcs  WGDC_StoreBoostErrTimer	    ; branch if lower
	cmpb INCLIM_UpperLimitOnWastegateDutyCycleCorrection	; compare b with memory contents (data is ff)
	bcc  WGDC_ClearBoostErrTimer	    ; branch if greater or equal
	incb		
WGDC_UpdateAdaptiveWGControlMemory:
	stab 0x00,x	
WGDC_ClearBoostErrTimer:
	clra		    ; a = 0
WGDC_StoreBoostErrTimer:
	staa Timer_BoostErrTimer    ; store a into memory
	ldaa Temp4	    ; load a with memory contents
	subb #0x80	    ;  -10000000-
	bmi  L1877	    ; branch if minus(hi bit 1)
	aba		    ; a=a+b
	bcs  WGDC_LoadMaxWGDutyCycle	    ; branch if lower
	cmpa #0xc8	    ; compare a with value -11001000-
	bls  WGDC_IncludeWGDutyCycleFromKnock	    ; branch if lower or same
WGDC_LoadMaxWGDutyCycle:
	ldaa #0xc8	    ; load a with value -11001000-
	bra  WGDC_IncludeWGDutyCycleFromKnock	    ; branch

L1877:	negb
	sba		    ; subtract (a=a-b)
	bcc  WGDC_IncludeWGDutyCycleFromKnock	    ; branch if greater or equal
	clra		    ; a = 0
WGDC_IncludeWGDutyCycleFromKnock:
	suba WastegateDutyCycleIncreaseFromKnock
	bcc  WGDC_StoreWGDutyCycle	    ; branch if greater or equal
	clra		    ; a = 0

WGDC_StoreWGDutyCycle:
	jsr  CallAndReturn1    ; call subroutine
	staa CurrentWastegateDutyCycle	 ; store a into memory
	rts		    ; return from subroutine
	
CalcWGDutyCycleT2:
	brset *BitFlags_54, #b54_FuelEngineNotRunning, T2WGDC_ClearWGDutyCycleVars	; branch if bit(s) set
        ldaa BoostTarget
        staa Temp3

        ldab Counter_MainLoop         ; load b with memory contents
        ldaa MapValue                  ; load a with memory contents
        suba BaroPressure
        bcs  T2WGDC_ClearWGDutyCycleVars                     ; branch if lower
        cmpa MAPPT2_WastegateDutyCycleMapSwitchPoint2    ; compare a with memory contents (data is 2e)
        bcc  L7739                     ; branch if greater or equal

T2WGDC_ClearWGDutyCycleVars:
        clra                           ; a = 0
        staa CurrentWastegateDutyCycle ; store a into memory
        staa WastegateDutyCycleIncreaseFromKnock    ; store a into memory
        staa Timer_Over5PsiBoostMaxFF  ; store a into memory
        bitb #0x1f                     ;  -00011111-
        bne  L7740                     ; branch if not equal (not zero)
        ldaa Timer_BoostTimer          ; load a with memory contents
        beq  L7740                     ; branch if equal (zero)
        deca                           ; decrement a
        staa Timer_BoostTimer          ; store a into memory
L7740:  rts                            ; return from subroutine

L7739:  cmpa T2KNOKMP_MinimumBoostToCountKnockEvents    ; compare a with memory contents (data is 23)
        bcc  L7742                     ; branch if greater or equal
        clra                           ; a = 0
        staa Timer_Over5PsiBoostMaxFF  ; store a into memory
L7742:  tstb
        bne  L7743                     ; branch if not equal (not zero)
        clra                           ; a = 0
        staa Timer_Over5PsiBoostMaxFF  ; store a into memory
L7743:  
        bitb #0x1f                     ;  -00011111-
        bne  L7744                     ; branch if not equal (not zero)
        ldab EngineRpm_HB                ; load b with memory contents
        cmpb T2RPMBST_MinimumRpmToTrackBoostCreep    ; compare b with memory contents (data is 4c)
        bcs  L7744                     ; branch if lower
        ldaa Timer_BoostTimer          ; load a with memory contents
        inca                           ; increment a
        beq  L7744                     ; branch if equal (zero)
        staa Timer_BoostTimer          ; store a into memory

L7744:
        ldaa MapValue       ; load a with memory contents
        suba BaroPressure   ; a = BoostOverBaro
        tab
        subb PreviousBoostOverBaro    ; b = BoostDelta_Signed
        staa PreviousBoostOverBaro    ; store a into memory
        stab BoostDelta_Signed    ; store b into memory
        tba

        staa Temp1        ; store a into memory
        bpl  L7745                     ; branch if plus (hi bit 0)
        nega                           ; negate a (set high bit)
L7745:  staa Temp0        ; store a into memory
        tst  Temp1
        bmi  L7746                     ; branch if minus(hi bit 1)
        ldaa EngineRpm_HB                ; load a with memory contents
        ldx  #T2RATLIM_OverboostPreventionRateLimit_FromRpm    ; load index with value
        jsr  Lookup4ByteTable               ; call subroutine
        ldaa Temp0        ; load a with memory contents
        cba
        bcs  L7746                     ; branch if lower
        ldaa T2PRTMAX_MaxWastegateDutyCycleforPartThrottleBoostCreep    ; load a with memory contents (data is c8)
        jsr  CallAndReturn1            ; call subroutine
        staa CurrentWastegateDutyCycle ; store a into memory
        rts                            ; return from subroutine

L7746:  clrb                           ; b = 0
        suba T2MPDEL_HysteresisForBoostCreep    ;  (data is 00)
        bls  L7747                     ; branch if lower or same
        staa Temp4        ; store a into memory
        ldaa Temp3        ; load a with memory contents
        suba MapValue
        adda #0x80                     ;  -10000000-
        ldx  #T2RESFAC_MapCorrectionResponseFactor_FromMap    ; load index with value
        jsr  Lookup4ByteTable               ; call subroutine
        ldaa Temp4        ; load a with memory contents
        mul                            ; multiply (d=a*b)
        tsta                           ; test a
        beq  L7748                     ; branch if equal (zero)
        ldab #0xff                     ; load b with value -11111111-
L7748:  tst  Temp1
        bmi  L7749                     ; branch if minus(hi bit 1)
        ldaa UPRLIM_UpperLimitOnMPCORR ; load a with memory contents (data is 10)
        bra  L7750                     ; branch

L7749:  
        ldaa LWRLIM_LowerLimitOnMPCORR ; load a with memory contents (data is 20)
L7750:  cba
        bcc  L7747                     ; branch if greater or equal
        tab                            ; b = a
L7747:  ldaa Temp3        ; load a with memory contents
        tst  Temp1
        bpl  T2WGDC_LookupWGDutyCycleBase                     ; branch if plus (hi bit 0)
        aba                            ; a=a+b
        bcc  L7752                     ; branch if greater or equal
        ldaa #0xff                     ; load a with value -11111111-
        bra  L7752                     ; branch

T2WGDC_LookupWGDutyCycleBase:
        sba                            ; subtract (a=a-b)
        bcc  L7752                     ; branch if greater or equal
        clra                           ; a = 0
L7752:  suba BaroPressure
        bcc  L7753                     ; branch if greater or equal
        clra                           ; a = 0
L7753:  ldx  #T2DCWOT_FullThrottleWastegateDutyCycle_C8is100Percent_FromMap    ; load index with value
        jsr  Lookup4ByteTable               ; call subroutine
        staa Temp4        ; store a into memory
        brclr *BitFlags_4f, #b4f_FullThrottle, L7754    ; branch if bit(s) clear
        ldaa EngineRpm_HB                ; load a with memory contents
        ldx  #T2DCWADJ_FullThrottleWastegateDutyCycleAdjustment_FromRpm    ; load index with value
        jsr  Lookup4ByteTable               ; call subroutine

        jsr  WGDC_AdjustWGDutyCycle

; instead of the delta to boost goal lookup, change this to an overshoot vs. rpm lookup
; if the actual boost is <= the boost target + overshoot, then set the DC to max (0xC8)
; this should help get the turbo up to boost and then switch over to the adaptives to 
; maintin the boost.
; 
        ldaa Temp3    ; load a with boost target
        suba MapValue
        bcc  L7838
        clra  ; if MAP is higher than boost target, set lookup reference to 0
L7838:  ldx  #T2DCWBST_FullThrottleWastegateDutyCycleAdjustment_FromBoostTarget        ; load index with value
        jsr  Lookup4ByteTable    ; call subroutine
        nega
        jsr  WGDC_AdjustWGDutyCycle

L7754:
        brclr *BitFlags_55, #b55_BoostOver5psi, L7758	 ; branch if bit(s) clear
	bclr *BitFlags_55, #b55_BoostOver5psi	 ; clear bits
        ldab WastegateDutyCycleIncreaseFromKnock    ; load b with memory contents
        addb T2KDCINC_WastegateDutyCycleIncreaseStepWhenKnocking    ;  (data is 04)
        bcc  L7759                     ; branch if greater or equal
        ldab #0xff                     ; load b with value -11111111-
L7759:  ldaa T2KDCMAX_WastegateDutyCycleIncreaseMaxWhenKnocking    ; load a with memory contents (data is 50)
        cba
        bcs  L7760                     ; branch if lower
        ldaa T2KDCMIN_WastegateDutyCycleIncreaseMinWhenKnocking    ; load a with memory contents (data is 0c)
        cba
        bcs  T2WGDC_StoreWGDutyCycleFromKnock                     ; branch if lower
L7760:  tab                            ; b = a
        bra  T2WGDC_StoreWGDutyCycleFromKnock                     ; branch

L7758:  ldx  #Cylinder2Retard-1  ; load index with value
T2WGDC_LookAtCylRetards:
        inx                            ; increment index (x=x+1)
        cpx  #Cylinder4Retard+1  ;  -00000000 10100111-
        beq  L7762                     ; branch if equal (zero)
        ldaa 0x00,x                    ; load a with memory at index + value
        anda #0x3f                     ; AND a with value -00111111-
        cmpa T2WGKNRD_MinimumKnockToReduceWGDC    ; compare a with memory contents (data is 07)
        bcs  T2WGDC_LookAtCylRetards      ; branch if lower
        
        ldab Counter_MainLoop         ; load b with memory contents
        bitb T2DECTIM_TimeScaleFor_DCDECK    ;  (data is 07)
        bne  L7763                     ; branch if not equal (not zero)
        ldab WastegateDutyCycleIncreaseFromKnock    ; load b with memory contents
        subb T2DCDECK_WastegateDutyCycleDecrementWhenSparkStillDerated    ; subtract memory contents from b (data is 02)
        bcc  T2WGDC_StoreWGDutyCycleFromKnock                     ; branch if greater or equal
L7762:  clrb                           ; b = 0

T2WGDC_StoreWGDutyCycleFromKnock:
        stab WastegateDutyCycleIncreaseFromKnock    ; store b into memory
L7763:  ldaa Temp3        ; load a with memory contents
        ldab BaroPressure              ; load b with memory contents
        addb T2MAPPT_WastegateDutyCycleMapSwitchPoint    ;  (data is 69)
        bcc  T2WGDC_SelectAdaptiveWGCell    ; branch if greater or equal
        ldab #0xff                     ; load b with value -11111111-

T2WGDC_SelectAdaptiveWGCell:
        ldx  #DCCOR1_AdaptiveWastegateCellBelowMAPPT    ; load index with value
        cba
        bcs  T2WGDC_LoadAdaptiveWGCell                     ; branch if lower
        inx                            ; increment index (x=x+1)
        ldab EngineRpm_HB                ; load b with memory contents
        cmpb DCRPM1_WastegateDutyCycleRpmBoundary1    ; compare b with memory contents (data is 7d)
        bcs  T2WGDC_LoadAdaptiveWGCell                     ; branch if lower
        inx                            ; increment index (x=x+1)
        cmpb DCRPM2_WastegateDutyCycleRpmBoundary2    ; compare b with memory contents (data is 9c)
        bcs  T2WGDC_LoadAdaptiveWGCell                     ; branch if lower
        inx                            ; increment index (x=x+1)
        cmpb DCRPM3_WastegateDutyCycleRpmBoundary3    ; compare b with memory contents (data is ac)
        bcs  T2WGDC_LoadAdaptiveWGCell                     ; branch if lower
        inx                            ; increment index (x=x+1)

T2WGDC_LoadAdaptiveWGCell:
        ldab 0x00,x                    ; load b with memory at index + value
        brset *Turbonator_Flags, #Turbonator_FuelOff, T2WGDC_ClearBoostErrTimer    ; branch if bit(s) set
        brset *Turbonator_Flags, #Turbonator_SparkCut, T2WGDC_ClearBoostErrTimer    ; branch if bit(s) set
        suba MapValue
        bhi  T2WGDC_BoostIsBelowTarget                     ; branch if higher

T2WGDC_BoostIsAboveTarget:
        nega                           ; negate a (set high bit)
        staa Temp1        ; store a into memory
	brset *BitFlags_52, #b52_WGDC, T2WGDC_IncrementWGAdaptive    ; branch needs to change for T2 style WG control
	bset *BitFlags_52, #b52_WGDC    ; set bits
        bra  T2WGDC_ClearBoostErrTimer                     ; branch

T2WGDC_IncrementWGAdaptive:
        ldaa T2MPDEL1_IncCounterWhenDeltaMapBelowThis    ; load a with memory contents (data is 02)
        cmpa Temp0        ; compare a with memory contents
        bcs  T2WGDC_ClearBoostErrTimer                     ; branch if lower
        ldaa Timer_BoostInErrorTimer   ; load a with memory contents
        inca                           ; increment a
        cmpa T2INCPT_AdaptiveIncAfterThisTime    ; compare a with memory contents (data is 0a)
        bcs  T2WGDC_StoreBoostErrTimer                     ; branch if lower
        ldaa Temp1        ; load a with memory contents
        cmpa T2MPROOF_StopAdaptiveWhenMapIsThisCloseToBoostTarget    ; compare a with memory contents (data is 02)
        bcs  T2WGDC_ClearBoostErrTimer                     ; branch if lower
        cmpb INCLIM_UpperLimitOnWastegateDutyCycleCorrection    ; compare b with memory contents (data is b0)
        bcc  T2WGDC_ClearBoostErrTimer                     ; branch if greater or equal
        incb
        bra  T2WGDC_UpdateAdaptiveWGControlMemory    ; branch

T2WGDC_BoostIsBelowTarget:
        staa Temp1        ; store a into memory
        brclr *BitFlags_52, #b52_WGDC, T2WGDC_DecrementWGAdaptive    ; branch if bit(s) clear
	bclr *BitFlags_52, #b52_WGDC    ; clear bits
        bra  T2WGDC_ClearBoostErrTimer                     ; branch

T2WGDC_DecrementWGAdaptive:
        ldaa WastegateDutyCycleIncreaseFromKnock    ; load a with memory contents
        bne  T2WGDC_ClearBoostErrTimer                     ; branch if not equal (not zero)
        brclr *BitFlags_4f, #b4f_FullThrottle, T2WGDC_ClearBoostErrTimer    ; branch if bit(s) clear
        ldaa EngineRpm_HB                ; load a with memory contents
        cmpa DCRPML_NoWastegateDutyCycleCorrectionBelowThisRpm    ; compare a with memory contents (data is 54)
        bcs  T2WGDC_ClearBoostErrTimer                     ; branch if lower
        cmpa DCRPMH_NoWastegateDutyCycleCorrectionAboveThisRpm    ; compare a with memory contents (data is bc)
        bhi  T2WGDC_ClearBoostErrTimer                     ; branch if higher
        ldaa MPDEL2_IncCounterWhenDeltaMapBelowThis2    ; load a with memory contents (data is 02)
        cmpa Temp0        ; compare a with memory contents
        bcs  T2WGDC_ClearBoostErrTimer                     ; branch if lower
        ldaa Timer_BoostInErrorTimer   ; load a with memory contents
        inca                           ; increment a
        cmpa DECPT_AdaptiveDecAfterThisTime    ; compare a with memory contents (data is 15)
        bcs  T2WGDC_StoreBoostErrTimer                     ; branch if lower
        ldaa Temp1        ; load a with memory contents
        cmpa T2MPFLOR_StopAdaptiveWhenMapIsThisCloseToBoostFloor    ; compare a with memory contents (data is 00)
        bcs  T2WGDC_ClearBoostErrTimer                     ; branch if lower
        cmpb DECLIM_LowerLimitOnWastegateDutyCycleCorrection    ; compare b with memory contents (data is 58)
        bls  T2WGDC_ClearBoostErrTimer                     ; branch if lower or same
        decb

T2WGDC_UpdateAdaptiveWGControlMemory:
        stab 0x00,x

T2WGDC_ClearBoostErrTimer:
        clra                           ; a = 0

T2WGDC_StoreBoostErrTimer:
        staa Timer_BoostInErrorTimer   ; store a into memory
        ldaa Temp4        ; load a with memory contents
        subb #0x80                     ;  -10000000-
        bmi  L7768                     ; branch if minus(hi bit 1)
        aba                            ; a=a+b
        bcs  T2WGDC_LoadMaxWGDutyCycle                     ; branch if lower
        cmpa #0xc8                     ; compare a with value -11001000-
        bls  T2WGDC_IncludeWGDutyCycleFromKnock                     ; branch if lower or same

T2WGDC_LoadMaxWGDutyCycle:
        ldaa #0xc8                     ; load a with value -11001000-
        bra  T2WGDC_IncludeWGDutyCycleFromKnock                     ; branch

L7768:  negb
        sba                            ; subtract (a=a-b)
        bcc  T2WGDC_IncludeWGDutyCycleFromKnock                     ; branch if greater or equal
        clra                           ; a = 0

T2WGDC_IncludeWGDutyCycleFromKnock:
        adda WastegateDutyCycleIncreaseFromKnock
        bcc  T2WGDC_StoreWGDutyCycle                     ; branch if greater or equal
        ldaa #0xff                     ; load a with value -11111111-

T2WGDC_StoreWGDutyCycle:
        jsr  CallAndReturn1            ; call subroutine
        staa CurrentWastegateDutyCycle ; store a into memory
        rts                            ; * there is still code after this instruction

InterruptVector_TimerOC2_Wastegate:
	ldx  #PIA1_PortB_DataDirection	  ; load index with value
	ldaa 0x01,x	    ; load a with memory at index + value
	staa Temp5	    ; store a into memory
	ldaa #0x64	    ; load a with value -01100100-
	ldab CurrentWastegateDutyCycle	 ; load b with memory contents
	cmpb #0x03	    ;  -00000011-
	bls  WG_SetOutput	    ; branch if lower or same
	cmpb #0xc5	    ;  -11000101-
	bcc  WG_ClearOutput	    ; branch if greater or equal
	brset *BitFlags_55, #b55_WastegateDC, L1881    ; branch if bit(s) set
	ldaa #0xc8	    ; load a with value -11001000-
	sba		    ; subtract (a=a-b)
WG_SetOutput:
	bset *BitFlags_55, #b55_WastegateDC    ; set bits
	bset  0, X, #pia1b_WastegateSolenoid    ; bit set
	bra  L1883	    ; branch

L1881:	tba		    ; a = b
WG_ClearOutput:
	bclr *BitFlags_55, #b55_WastegateDC    ; clear bits
	bclr  0, X, #pia1b_WastegateSolenoid    ; bit clear
L1883:	bclr  1, X, #pia1b_bit2    ; bit clear
	bset  0, X, #pia1b_WastegateSolenoid    ; bit set
	jsr  Delay32uSec    ; call subroutine
	clrb		    ; b = 0
	lsrd		    ; shift right (d=d/2)
	lsrd		    ; shift right (d=d/2)
	addd CPU_Timer_OC2_Wastegate
	std  CPU_Timer_OC2_Wastegate
	ldab BatteryVolts    ; load b with memory contents
	cmpb #0xa2	    ;  -10100010-
	bcs  L1884	    ; branch if lower
	bclr  0, X, #pia1b_WastegateSolenoid    ; bit clear
L1884:	ldaa #CPU_TIFlag1_OC2Wastegate	    ; clear the WG flag
	staa CPU_TimerInterruptFlag1
	ldaa Temp5	    ; load a with memory contents
	staa 0x01,x
	rti		    ; return from interrupt

; ***********************************************************************
;   ----------------------------------------------------
;	Additional code modules
;   ----------------------------------------------------
;   ----------------------------------------------------
;	Flash Check Engine Light on Knock Routine
;   ----------------------------------------------------
;
; This needs to be called somewhere in the MainProgramLoop,
; it is known to work when called at CalcBoostGoal_MM.
; PIA1_A_Buffer gets altered throughout the code, every
; time through the main loop these bits are copied to the
; actual hardware.
;
; To enable this code, simply check the Custom Options flag for it
; in the table file. This codebase has been modified to check for
; the option and will automatically re-config the SMEC appropriately.
;

UseCELForKnockIndication_MM:
        ldx   #OPTN1_CalCustomOptionConfigFlags1
	brclr 0, X, #opt_FlashCE, FlashCEL_OnKnock_return
	brset *BitFlags_54, #b54_FuelEngineNotRunning, FlashCEL_OnKnock_return	  ; branch if bit(s) set
	ldaa  CoolantTemp
	cmpa  KNKMIN_FlashCEMinTemp
	bcs   FlashCEL_OnKnock_return; cold motor creates a LOT of false positives
	ldaa  Cylinder2Retard	 ; load a with memory contents
	bne   KnockDetect_LightCEL	    ; branch if not equal (not zero)
	ldaa  Cylinder1Retard	 ; load a with memory contents
	bne   KnockDetect_LightCEL	    ; branch if not equal (not zero)
	ldaa  Cylinder3Retard	 ; load a with memory contents
	bne   KnockDetect_LightCEL	    ; branch if not equal (not zero)
	ldaa  Cylinder4Retard	 ; load a with memory contents
	bne   KnockDetect_LightCEL	    ; branch if not equal (not zero)
NoKnockDetect_UnlightCEL:		; fallthrough, extinguish light
	bset	*PIA1_A_Buffer, #pia1abuf_CELight
	bra	FlashCEL_OnKnock_return
KnockDetect_LightCEL:
	bclr	*PIA1_A_Buffer, #pia1abuf_CELight
FlashCEL_OnKnock_return:
	rts

;   -------------------------------------------------------
;	Launch Control Routine
;   -------------------------------------------------------
LaunchControl_MM:

        ldx   #Turbonator_Flags
	brclr *TimerOverflowsBetweenDistPulses, #$%11111111, LaunchControl_CheckEnable    ; branch if bit(s) clear
        bra   LaunchControl_Off

LaunchControl_CheckEnable:
        ldaa  OPTN2_CalCustomOptionConfigFlags2
        bita  #opt_StageLim ; do these all need to be here? Or just the stagelim optn?
        bne   LaunchControl_CheckSwitch       ; run the rev limiter code
        bra   LaunchControl_Off

LaunchControl_CheckSwitch:
        ; check to see if no switch is selected, if no switch, assume speed cutoff only
        ldab  STGSWS_StagingLimiterEnableSwitch
        beq   LaunchControl_CheckTPS ; branch if no switch bit is set

        ; if there is a switch specified, check it against the switch port to see if it's 'on'
	bitb  SwitchPortAccessReg
        beq   LaunchControl_Off
        
LaunchControl_CheckTPS:
        ldab  TpsVolts
        subb  MINTHR_LowestSessionTPS
        bcs   LaunchControl_Off ; turn off launch control if TPS is lower than MINTHR
        cmpb  STGTPS_StageLimiterMinTPS ; to prevent the lauch control from coming on at idle
        bcs   LaunchControl_Off ; brach if TPS over MINTHR is less than threshold

LaunchControl_CheckSpeed:
	ldd   VehicleSpeed_HB	               ; load d (a&b) with memory contents
	asld		                       ; shift right (d=d*2)
	asld		                       ; shift right (d=d*2)
	cmpa  STGSPD_StageLimiterCutoffSpeed    ; compare a with memory contents (data is 0a)
	bcc   LaunchControl_Off		       ; branch if the vehicle speed is greater than the cutoff speed

LaunchControl_On:
        bset  0, x, #Turbonator_Staging         ; set the flag to indicate that the staging limiter conditions are met
	bra   LaunchControl_DecideEngineOnOff   ; branch

LaunchControl_Off:
        clr   Counter_SparkCut
        bset  *Pattern_SparkCut, #bit_all
        bclr  0, x, #Turbonator_Staging         ; clear the flag indicating the staging limiter conditions are NOT met
        bra   LaunchControl_AllowFuelSpark

LaunchControl_DecideEngineOnOff:
	brclr 0, x, #Turbonator_FuelOff | Turbonator_SparkCut, LaunchControl_CheckUpperRPM    ; branch if bit(s) clear
        jmp   LaunchControl_CheckLowerRPM

LaunchControl_CheckUpperRPM:
	ldaa  EngineRpm_HB                      ; load a with memory contents
	cmpa  STGROF_StageLimiterRPMOffSetpoint ; compare a with memory at index + value
	bcs   LaunchControl_AllowFuelSpark      ; branch if launch control RPM is greater than current RPM

LaunchControl_ShutOffFuelSpark:
        ldaa  OPTN2_CalCustomOptionConfigFlags2
        bita  #opt_FuelRevLim
        beq   LaunchControl_CheckSparkCut       ; don't turn off the fuel...
        bset  0, x, #Turbonator_FuelOff         ; set bits

LaunchControl_CheckSparkCut:
        bita  #opt_SprkRevLim
        beq   LaunchControl_Return              ; don't turn off the spark...
        bset  0, x, #Turbonator_SparkCut        ; new T-SMEC Spark rev limiter
        bra   LaunchControl_Return

;LaunchControl_UseHysteresisToDetermineWhenToTurnFuelBackOn:
;        brclr *Turbonator_Flags, #Turbonator_OverRev, LaunchControl_CheckLowerRPM    ; branch if bit(s) clear
;	brclr *BitFlags_50, #b50_FallToIdle, LaunchControl_Off    ; branch if bit(s) clear

LaunchControl_CheckLowerRPM:
        ldaa  EngineRpm_HB    ; load a with memory contents
	cmpa  STGRON_StageLimiterRPMOnSetpoint  ; compare a with memory at index + value
	bcc   LaunchControl_Return	       ; branch if RPM is higher than OFF point

LaunchControl_AllowFuelSpark:
        bclr  0, x, #Turbonator_FuelOff | Turbonator_SparkCut ; new T-SMEC Spark rev limiter

LaunchControl_Return:
	rts		                       ; return from subroutine

;   -------------------------------------------------------
;	Anti-Lag Retard Routine
;   -------------------------------------------------------
CalculateSparkCutandAntiLagRetard_Routine:
 
        ; ******************************************************************
        ; Called from the falling edge interrupt sevice routine...
        ; on entry and exit, accA contains the total timing (don't use accA for anything else in this routine!)
        ; if anti-lag should be on, substitute the antilag value for the total timing
        ; otherwise return the original
        
        ; Rotating spark cut:
        ; 2 address tables, one containing the 'value', 1 the 'base';
        ; 'base' is used to count (counter init)
        ; 'value' is rotated (ROLx), the result in carry is used to determine if the cylinder should be allowed to fire this time.
        ; When the count = base, then reset the counter and reload the pattern
        ;
        ; The 'Spark Cut Fraction' value is now simply a pointer to the pattern and counter base.

        ; Patterns:

        ; 1/3 - 011  00000; index = 0; value = 96(0x60); base = 3+1
        ; 2/3 - 001  00000; index = 1; value = 32(0x20); base = 3+1
        ; 3/5 - 00101  000; index = 2; value = 40(0x28); base = 5+1
        ; 4/5 - 01000  000; index = 3; value = 64(0x40); base = 5+1
        ; 3/7 - 0011011  0; index = 4; value = 54(0x36); base = 7+1
        ; 4/7 - 0010101  0; index = 5; value = 42(0x2a); base = 7+1
        ; 5/7 - 0010001  0; index = 6; value = 34(0x22); base = 7+1
        ; 6/7 - 0001000  0; index = 7; value = 16(0x10); base = 7+1
        
        ; Other patterns or modified patterns are also possible.

        ; ******************************************************************
        ; check spark and anti-lag enable conditions

        ldx  #Turbonator_Flags
        bclr 0x00, x, #Turbonator_AntiLag ; clear the antilag flag since it hasn't been determined yet
        bset  0x00, x, #Turbonator_AllowSpark ; spark is allowed normally
        brclr 0x00, x, #Turbonator_Staging, AntiLag_Return 	 ; don't do anything unless we're staging, normal spark
        brclr 0x00, x, #Turbonator_SparkCut, CalulateLaunchAdvance ; branch if the spark cut isn't on right now - check for anti-lag conditions since we are staging
        bclr  0x00, x, #Turbonator_AllowSpark ; spark cut is on, so clear the 'allow' flag

RotateSparkCutPattern:
        ; counter works because this routine is called from the rising edge routine - once per cylinder
        ldab Counter_SparkCut
        beq  SetBaseandPattern
        dec  Counter_SparkCut
        rol  Pattern_SparkCut ; if we should have spark, then the carry bit will be set after the rotate
        bcc  CalulateLaunchAdvance ; if carry is now set, then allow spark...

AllowSparkThisRotation:
        bset 0x00, x, #Turbonator_AllowSpark ; allow spark for just this revolution...

        ; check that antilag is enabled

CalulateLaunchAdvance:
        ldx  #OPTN2_CalCustomOptionConfigFlags2
        brclr 0x00, X, #opt_AntiLag, AntiLag_Return

        ldab ANLGRP_AntiLagRetardRPM
        cmpb EngineRpm_HB
        bcc  AntiLag_Return ; branch if
        ldaa ANTLAG_AntiLagRetardAbs
        asra
        asra ; divide by 4 - min/max = +/-16 deg
        adca #0x00 ; round up any remainder
        ldx  #Turbonator_Flags
        bset 0x00, x, #Turbonator_AntiLag ;just to indicate that the anti-lag is active, for logging purposes

AntiLag_Return:
        rts
        
SetBaseandPattern:
        ldab SPKFRC_SparkCutFraction ; this is now an offset value
        ldy  #LNCBDT_BaseDataTable
        aby
        ldab 0x00, Y ; b now contains the pattern
        stab Counter_SparkCut

        ldab SPKFRC_SparkCutFraction ; this is now an offset value -- oops, this was left off, made the pattern wrong
        ldy  #LNCPDT_PatternDataTable
        aby
        ldab 0x00, Y ; b now contains the base value
        stab Pattern_SparkCut ; need new RAM location for this
        bra  CalulateLaunchAdvance 
        
        
;   -------------------------------------------------------
;	Wideband Transfer Function Routine
;   -------------------------------------------------------
;
; This rotuine converts a WB input signal to a NBO2 type of signal for ue with the stock O2 controller.
; Converts the WB signal to an AFR for different sensor types/outputs; can be logged.
; Has an option for a NB offset to allow twaeking of the rich/lean condition

ConvertWB2NBSignal_MM:

        ldaa RawAirFuelSensInput
        ldab OPTN2_CalCustomOptionConfigFlags2    ; load a with memory contents (data is 9f)
        bitb #opt_WB2NB                           ;  -00000001-
        beq  WB2NB_Return                         ; branch if equal (zero)

LookupWB2NBXferFunc:

        ldx  #WB2AFR_WidebandToAFRTransferFunction  ; load index with value
        jsr  Lookup4ByteTable                     ; call subroutine
        staa AFRatio
        ldx  #AFR2NB_WidebandAFRToO2TransferFunction  ; load index with value
        jsr  Lookup4ByteTable                     ; call subroutine
        adda NBOFFS_NarrowBandOffsetValue

WB2NB_Return:
        staa O2SensorValue
        rts                            ; * there is still code after this instruction

;   -------------------------------------------------------
;	Nitrous Retard Routine
;   -------------------------------------------------------
;
; This routine will retard timing a set amount based on a switch input. 
;

CalculateNO2Retard_Routine_MM:

       clra  ; so that we can clear the NO2Retard if not used

NO2_CheckOptions:
       ldx  #OPTN1_CalCustomOptionConfigFlags1
       brclr 0, X, #opt_NO2Retard, NO2_SaveRetardValue

NO2_CheckSwitch:
       ldab SwitchPortAccessReg    ; load b with memory contents
       brclr 0, X, #opt_NO2Pol, NO2_Polarity_Lo ; check the switch polarity

NO2_Polarity_Hi:
       bitb NO2SWS_NO2SwitchSelect
       beq  LoadNO2Retard	    ; branch if equal (zero)
       bra  NO2_SaveRetardValue

NO2_Polarity_Lo:
       bitb NO2SWS_NO2SwitchSelect
       bne  LoadNO2Retard	    ; branch if not equal (not zero)
       bra  NO2_SaveRetardValue

LoadNO2Retard:
       ldaa NO2RET_NO2RetardConstant
       asra
       asra
       asra                         ; divide constant by 8 --> constant range is 0 to 15 deg...

NO2_SaveRetardValue:
       staa NO2Retard               ; store the antilag retard
       rts


;   -------------------------------------------------------
;	PTU (Lock-Up Converter) Control Routine
;   -------------------------------------------------------
;
; This code is largely copied over from the TBI SMEC code. It is very similar to
; the code used in the '90/91 SBEC T1 cars that have PTU from the factory. The table
; and constant values (defined above) are the same as the 'leftover' PTU data included
; with the SMEC T1 cals and as the working SBEC T1 cals.
;
; There is an output overlap between the PTU output and the EMR. So, the EMR code will
; have to be dis-abled if built using the PTU output control.

ControlPTU_MM:
        ldab CONFIG_ConfigurationFlags          ; load b with memory contents (data is bf)
        bitb #cfg_PTU       ;  -00010000-
        beq  LD4DF          ; branch if equal (zero)
        jmp  PTU_Main

LD4DF:  ldaa ATMOffset      ; load a with memory contents
        cmpa #0x16          ; compare a with value -00010110-
        beq  LD4E9          ; branch if equal (zero)
        cmpa #0x14          ; compare a with value -00010100-
        bne  PTU_SetPTUBits ; branch if not equal (not zero)
LD4E9:  rts                 ; return from subroutine

PTU_Main:
        ldaa PTU_MapTemp    ; load a with memory contents
        staa Temp0          ; store a into memory
        ldaa Counter_MainLoop    ; load a with memory contents
        anda PTUCNI_PTUCounterTimerIntervalForLoop          ;  (data is 07)
        bne  PTU_CheckThrottleForLock          ; branch if not equal (not zero)
        ldaa MapValue       ; load a with memory contents
        staa PTU_MapTemp    ; store a into memory

PTU_CheckThrottleForLock:
        ldaa TpsVolts       ; load a with memory contents
        suba MINTHR_LowestSessionTPS
        bls  PTU_SetPTUBits          ; branch if lower or same
        staa Temp4          ; store a into memory
        ldaa CoolantTemp    ; load a with memory contents
        cmpa PTUMTP_PTUMinLockTemperature          ; compare a with memory contents (data is c5)
        bcs  PTU_SetPTUBits          ; branch if lower
        brclr *BitFlags_AIS, #b0c_ATXInGear, PTU_SetPTUBits    ; branch if bit(s) clear
        brset *StartupSwitchMirror1, #sw1_Brake, PTU_SetPTUBits    ; branch if bit(s) set
        ldd  VehicleSpeed_HB    ; load d (a&b) with memory contents
        asld                ; shift left (d=d*2)
        asld                ; shift left (d=d*2)
        asld                ; shift left (d=d*2)
        cmpa PTUMSP_PTUMinLockSpeed          ; compare a with memory contents (data is 68)
        bcc  PTU_CheckMAPThresholdsForLock          ; branch if greater or equal
        ldaa MapValue       ; load a with memory contents
        suba Temp0
        bcs  PTU_CheckMAPThresholdsForLock          ; branch if lower
        cmpa PTUMP3_PTUMAPThresholdForLock3          ; compare a with memory contents (data is 20)
        bcc  PTU_SetPTUBits          ; branch if greater or equal
        bra  LD63A          ; branch

PTU_SetPTUBits:
        clra                ; a = 0
        staa Counter_PartThrottleUnlock    ; store a into memory
        bset *PIA1_A_Buffer, #pia1abuf_PartThrotUnlock    ; set bits
        bclr *BitFlags_52, #b52_PTU_B | b52_PTU_A    ; clear bits
        rts                 ; return from subroutine

PTU_CheckMAPThresholdsForLock:
        ldaa Temp0          ; load a with memory contents
        suba MapValue
        bcs  LD63A          ; branch if lower
        staa Temp0          ; store a into memory
        ldx  #PTUMP1_PTUMAPThresholdForLock1        ; load index with value
        brset *BitFlags_52, #b52_PTU_B, LD632    ; branch if bit(s) set
        brset *BitFlags_52, #b52_PTU_A, LD631    ; branch if bit(s) set
        ldaa Temp4          ; load a with memory contents
        cmpa PTUDTP_PTUDeltaTPSForUnlock          ; compare a with memory contents (data is 26)
        bcs  LD62E          ; branch if lower
        bset *BitFlags_52, #b52_PTU_B    ; set bits
        bra  LD632          ; branch

LD62E:  bset *BitFlags_52, #b52_PTU_A    ; set bits
LD631:  inx                 ; increment index (x=x+1)
LD632:  ldab Temp0          ; load b with memory contents
        cmpb 0x00,x     
        bcc  PTU_SetPTUBits ; branch if greater or equal
        bra  PTU_CheckCounter          ; branch

LD63A:  bclr *BitFlags_52, #b52_PTU_B | b52_PTU_A    ; clear bits
PTU_CheckCounter:
        ldaa Counter_PartThrottleUnlock    ; load a with memory contents
        cmpa #0x01          ; compare a with value -00000001-
        bls  PTU_CheckThresholdsForUnlock          ; branch if lower or same
        deca                ; decrement a
        staa Counter_PartThrottleUnlock    ; store a into memory
        rts                 ; return from subroutine

PTU_CheckThresholdsForUnlock:
        ldx  #PTUUUL_UpperLimitForPTUUnlock        ; load index with value
        brclr *PIA1_A_Buffer, #pia1abuf_PartThrotUnlock, LD651    ; branch if bit(s) clear
        ldx  #PTULUL_UpperLimitForPTULock        ; load index with value
LD651:  bsr  PTU_LookupPTUParam          ; call subroutine
        bcc  PTU_SetPTUBits ; branch if Temp4 (Delta TPS) < lookup value
        ldx  #PTUULL_LowerLimitForPTUUnlock        ; load index with value
        brclr *PIA1_A_Buffer, #pia1abuf_PartThrotUnlock, LD65F    ; branch if bit(s) clear
        ldx  #PTULLL_LowerLimitForPTULock        ; load index with value
LD65F:  bsr  PTU_LookupPTUParam          ; call subroutine
        bcs  PTU_SetPTUBits ; branch if Temp4 (DeltaTPS) > lookup value
        ldaa Counter_PartThrottleUnlock    ; load a with memory contents
        beq  PTU_CheckVehicleSpeed          ; branch if equal (zero)
        bclr *PIA1_A_Buffer, #pia1abuf_PartThrotUnlock    ; clear bits
        rts                 ; return from subroutine

PTU_CheckVehicleSpeed:
        ldd  VehicleSpeed_HB    ; load d (a&b) with memory contents
        asld                ; shift left (d=d*2)
        asld                ; shift left (d=d*2)
        asld                ; shift left (d=d*2)
        ldab PTUCNH_PTUCounterHiSpeed          ; load b with memory contents (data is 5b)
        cmpa PTUMSP_PTUMinLockSpeed          ; compare a with memory contents (data is 68)
        bcc  LD67B          ; branch if greater or equal
        ldab PTUCNL_PTUCounterLoSpeed          ; load b with memory contents (data is b5)
LD67B:  stab Counter_PartThrottleUnlock    ; store b into memory
        rts                 ; return from subroutine

PTU_LookupPTUParam:
        ldd  VehicleSpeed_HB    ; load d (a&b) with memory contents
        asld                ; shift left (d=d*2)
        asld                ; shift left (d=d*2)
        asld                ; shift left (d=d*2)
        jsr  Lookup4ByteTable          ; call subroutine
        ldaa Temp4          ; load a with memory contents
        cba                 ; set the flags as if A-B
        rts                 ; return from subroutine

;   -------------------------------------------------------
;	Shift Light Control Routine
;   -------------------------------------------------------
;
;
; This routine will control a shift light with many parameters
; configurable by the user/calibrator.
;
; Here's how I think this should work:
;
; 1) 2 setpoints for the shift light; 1 for 1st gear, one for all other gears
; 2) adjustable by the driver - special mode?
;    - special mode: when the engine is not running, press and hold the brake pedal, push cruise set (?) button
;    - to increment the shift light point; display the value on the tach?
; 3) option to flash the light 3 times before the shift, based on rpm
; 4) user/calibrator selectable output (cruise solenoids, purge solenoids, egr solenoid, or PTU output, EMR output, etc.)
; 5) will require 2 routines; 1 for running the light, the other for setup.

; ControlShiftLight_MM:
;        brclr *Counter_MainLoop, #$%00100000, ShiftLight_Return
;        ldx   OPTN1_CalCustomOptionConfigFlags1
;        brclr 0, X, #opt_ShiftLight, ShiftLight_Return
;        brclr *BitFlags_54, #b54_FuelEngineNotRunning, ShiftLight_Run
; 
; ShiftLight_Setup:
;        ; still need to figure this out...
;        ;
;        ; use brake pedal to engage the setup, and the throttle to adjust?
;        ; press brake pedal 3 times in 2 sec to engage setup (with engine not running, obviously)
;        ; then press throttle to indicate shift rpm on tach and press brake again to set
;        ; to set 2nd point, press brake 4 times in 2 sec, otherwise same procedure...
;        ;
;        ; need to figure out how to time the tach pulses to do this right, might be difficult to do
;        ;
;        ; for testing, I can do this with only constants, not variables...
;        ; should run with only this line in the "setup" routine...
; 
;        bra ShiftLight_Return
; 
; ShiftLight_Run:
;        ldx  EngineRpm_HB
;        cpx  SLRPM_ShiftLightSetpoint
;        bcc  ShiftLight_TurnLightOff
; 
; ShiftLight_TurnLightOn:
;        bset *PIA1_A_Buffer, #pia1abuf_PartThrotUnlock
;        bra  ShiftLight_Return
; 
; ShiftLight_TurnLightOff:
;        bclr *PIA1_A_Buffer, #pia1abuf_PartThrotUnlock
; 
; ShiftLight_Return:
;        rts

; ********************************
; Alky Injection Control Routines
; ********************************
; 
; ********************
; pump control routine
; ********************
; 
; MM_AlkyPump_Control:
; 
;         ldaa CONFIG_ConfigurationFlags
;         bita #cfg_AlkyInj           ; check the bit for Alky Injection
;         beq  AlkyPump_Return        ; branch if the bit is not set, ie not enabled
;         bita #cfg_SpeedSenseAero    ; check the bit for Speed Sensitive Aero
;         bne  AlkyPump_Return        ; branch if the bit is set, can't run both of these routines
; 
;         ldaa MapValue
;         ldab Z83_PortA_copy
;         cmpa AKPMON_AlkyPumpOnSetpointFromMAP
;         bcs  AlkyPump_CheckHysteresisAndTurnOff ;if MAP is    lower than the setpoint, see if it's lower than the 'off' point
;         orab #PortA_PurgeEGR ;or whichever output you're going to use, this sets the bit to turn on the pump
;         stab Z83_PortA_copy
;         jmp  AlkyPump_Return
; 
; AlkyPump_CheckHysteresisAndTurnOff:
;         cmpa AKPMOF_AlkyPumpOffSetpointFromMAP
;         bcc  AlkyPump_Return ; MAP is still higher than the 'off' setpoint
;         andb ~#PortA_PurgeEGR ;turn off the pump
;         stab Z83_PortA_copy
; 
; AlkyPump_Return:
;         rts
;    
; ************************
; injector control routine
; ************************
;          ; these are just messages to display during assemble to let you know what's going on...
; 
; MM_AlkyInjector_Control:
; 
; first, check to see if inj1 is already on, if it is, then check to see if it needs to be turned off, then maybe check inj2 turn on
;         ldaa CONFIG_ConfigurationFlags
;         bita #cfg_AlkyInj           ; check the bit for Alky Injection
;         beq  AlkyInj_Return        ; branch if the bit is not set, ie not enabled
;         bita #cfg_SpeedSenseAero    ; check the bit for Speed Sensitive Aero
;         bne  AlkyInj_Return        ; branch if the bit is set, can't run both of these routines
; 
;         ldab Z83_PortA_copy
;         orab #PortA_CruiseVent ;clear all bits in A except for this one
;         andb #PortA_CruiseVent
;         bne  AlkyInj1_CheckHysteresisAndTurnOff ;branch if the bit for inj1 is set
; 
; inj1 is not already on, so check the MAP level
; 
;         ldaa MapValue
;         cmpa AKI1ON_AlkyInj1OnSetpointFromMAP
;         bcs  AlkyInj1_CheckHysteresisAndTurnOff ;if MAP is lower than the setpoint, see if it's lower than the 'off' point
;         orab #PortA_CruiseVent ;or whichever output you're going to use, this sets the bit to turn on inj 1
;         stab Z83_PortA_copy
;         jmp  AlkyInj_Return
; 
; AlkyInj1_CheckHysteresisAndTurnOff:
;         cmpa AKI1OF_AlkyInj1OffSetpointFromMAP
;         bcc  AlkyInj_Return ; MAP is still higher than the 'off' setpoint
;         andb ~#PortA_CruiseVent ;turn off inj 1
;         stab Z83_PortA_copy
; 
; AlkyInj_CheckInj2:
;         ldaa MapValue
;         cmpa AKI2ON_AlkyInj2OnSetpointFromMAP
;         bcs  AlkyInj2_CheckHysteresisAndTurnOff ;if MAP is lower than the setpoint, see if it's lower than the 'off' point
;         orab #PortA_CruiseVac ;or whichever output you're going to use, this sets the bit to turn on inj 2
;         stab Z83_PortA_copy
;         jmp  AlkyInj_Return
; 
; AlkyInj2_CheckHysteresisAndTurnOff:
;         cmpa AKI2OF_AlkyInj2OffSetpointFromMAP
;         bcc  AlkyInj_Return ; MAP is still higher than the 'off' setpoint
;         andb ~#PortA_CruiseVac ;turn off inj 1
;         stab Z83_PortA_copy
; 
; AlkyInj_Return:
;         rts

;   -------------------------------------------------------

    .org	0HFEA0
BoostButtonCopyrightNotice:
    .str	"Turbonator mods and brand Copr. 2013 Rob Lloyd"
    .str        "Turbonator SMEC v19"

    .org	0Hff00
ChryslerCopyrightNotice:
    .str	"COPR. 1988 CHRYSLER CORP."


    .org    0Hffd6
vectors:
;SCI_Interrupt_vector:
    .word   Interrupt_RealTime
;SPIE_Flag_Interrupt_vector:
    .word   Interrupt_RealTime
;PAII_Flag_Interrupt_vector:
    .word   Interrupt_PulseAccumulatorInputEdge
;PAOVI_Flag_Interrupt_vector:
    .word   Interrupt_PulseAccumulatorOverflow
;TOI_Flag_Interrupt_vector:
    .word   Interrupt_RealTime
;OC5_Flag_Interrupt_vector:
    .word   InterruptVector_DwellTimer
;OC4_Flag_Interrupt_vector:
    .word   Interrupt_TimerOutputCapture4
;OC3_Flag_Interrupt_vector:
    .word   Interrupt_TimerOutputCapture3
;OC2_Flag_Interrupt_vector:
    .word   InterruptVector_TimerOC2_Wastegate
;OC1_Timer_Interrupt_vector:
    .word   Interrupt_TimerOutputCapture1
;IC3_Timer_Interrupt_vector:
    .word   Interrupt_TimerInputCapture3
;IC2_Timer_Interrupt_vector:
    .word   InterruptVector_SpeedometerSignal
;IC1_Timer_Interrupt_vector:
    .word   InterruptVector_DistributorSignal
;Realtime_Interrupt_vector:
    .word   Interrupt_RealTime
;IRQ_hardware_Interrupt_vector:
    .word   InterruptVector_PIA_Signal
;XIRQ_hardware_Interrupt_vector:
    .word   Interrupt_XIRQ
;SWI_Software_Interrupt_vector:
    .word   Interrupt_Software
;Illegal_Opcode_vector:
    .word   Interrupt_BadOp
;COP_Watchdog_Timeout_vector:
    .word   Interrupt_COPFail
;Clock_Monitor_Fail_vector:
    .word   Interrupt_SoftwareFail
;ResetVector:
    .word   Interrupt_RealTime
    
        .msg "Complete."


; Quick 68HC11 reference:
;   a	Accumulator A (8-bit)
;   b	Accumulator B (8-bit)
;   d	A and B combined (16-bit, A hi, B lo)
;   ccr Condition Code Register (8-bit, CCR)
;   pc	Program Counter (16-bit)
;   sp	Stack Pointer (16-bit)
;   ix	Index Register X (16-bit)
;   iy	Index Register Y (16-bit)
;
; some RAM bytes from 0000 are kept alive by standby battery power.
; 
;   0000 to 00ff - 256 bytes of internal RAM
;   ffd6 to ffff - Interrupt vectors (TechRef Chapter 5)
;   ------------
;   ffd6 to ffd7 - SCI Interrupt vector: b33a
;   ffd8 to ffd9 - SPIE Flag Interrupt vector: b33a
;   ffda to ffdb - PAII Flag Interrupt vector: b308
;   ffdc to ffdd - PAOVI Flag Interrupt vector: b2f6
;   ffde to ffdf - TOI Flag Interrupt vector: b33a
;   ffe0 to ffe1 - OC5 Flag Interrupt vector: bd17
;   ffe2 to ffe3 - OC4 Flag Interrupt vector: b305
;   ffe4 to ffe5 - OC3 Flag Interrupt vector: b302
;   ffe6 to ffe7 - OC2 Flag Interrupt vector: c7c6
;   ffe8 to ffe9 - OC1 Timer Interrupt vector: 8900
;   ffea to ffeb - IC3 Timer Interrupt vector: b2ff
;   ffec to ffed - IC2 Timer Interrupt vector: bdad
;   ffee to ffef - IC1 Timer Interrupt vector: ae92
;   fff0 to fff1 - Realtime Interrupt vector: b33a
;   fff2 to fff3 - IRQ hardware Interrupt vector: c49d
;   fff4 to fff5 - XIRQ hardware Interrupt vector: b2f0
;   fff6 to fff7 - SWI Software Interrupt vector: b2ed
;   fff8 to fff9 - Illegal Opcode vector: b2f9
;   fffa to fffb - COP Watchdog Timeout vector: b2f3
;   fffc to fffd - Clock Monitor Fail vector: b2fc
;   fffe to ffff - Power on or external Reset vector: b33a
;   ------------

