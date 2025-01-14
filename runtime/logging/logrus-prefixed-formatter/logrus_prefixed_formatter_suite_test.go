package prefixed_test

import (
	"testing"

	. "github.com/onsi/ginkgo"
	. "github.com/onsi/gomega"
)

type LogOutput struct {
	buffer string
}

func (o *LogOutput) Write(p []byte) (int, error) {
	o.buffer += string(p)
	return len(p), nil
}

func (o *LogOutput) GetValue() string {
	return o.buffer
}

func TestLogrusPrefixedFormatter(t *testing.T) {
	RegisterFailHandler(Fail)
	RunSpecs(t, "LogrusPrefixedFormatter Suite")
}
