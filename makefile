RM := rm -rf
SUBDIRS := \
src \

# Add inputs and outputs from these tool invocations to the build variables 
CPP_SRCS := \
./src/strategy.cpp \
./src/basic_types.cpp \
./src/component_management.cpp \
./src/component_types.cpp \
./src/instance.cpp \
./src/main.cpp \
./src/solver.cpp 

OBJS := \
strategy.o \
basic_types.o \
component_management.o \
component_types.o \
instance.o \
main.o \
solver.o 

CPP_DEPS := \
strategy.d \
basic_types.d \
component_management.d \
component_types.d \
instance.d \
main.d \
solver.d 

%.o: ./src/%.cpp
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C++ Compiler'
	g++ -O3 -DNDEBUG -std=c++11 -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@:%.o=%.d)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '

LIBS := -lgmpxx -lgmp

# All Target
all: SharpSSAT

# Tool invocations
SharpSSAT: $(OBJS) 
	@echo 'Building target: $@'
	@echo 'Invoking: GCC C++ Linker'
	g++ -L/usr/lib/ -o "SharpSSAT" $(OBJS) $(LIBS)
	@echo 'Finished building target: $@'
	@echo ' '

# Other Targets
clean:
	-$(RM) $(OBJS)$(CPP_DEPS) SharpSSAT
	-@echo ' '

.PHONY: all clean dependents

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(strip $(CPP_DEPS)),)
-include $(CPP_DEPS)
endif
endif